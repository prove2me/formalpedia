-- Prove2me | Theorems.Thm_GuanQinQDP_Restricted_Supplement_unrestricted_composition
-- name    : GuanQinQDP.Restricted.Supplement.unrestricted_composition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:37:08.386492+00:00
-- url     : https://prove2.me/theorems/48d38a5b-e636-47b8-b991-2aefbdf58042
-- title:
--   Theorem 5.5 — unrestricted approximate composition with $\gamma'=\gamma G_i/(1+(G_i-1)\delta)$, $\delta'=G_i\delta/(1+(G_i-1)\delta)$
-- statement:
--   Let $A=\bigotimes_{j=1}^nA_j$ be a tensor product of qubit channels $A_j:M_2\to M_2$, acting on arbitrary, possibly entangled, inputs on $(\mathbb C^2)^{\otimes n}$. Fix a register $i$, a real $\gamma>0$ and a real $\delta$, and suppose:
--
--   1. $A_i$ on its own is $(\log\gamma,\delta)$-QDP: $\operatorname{Tr}[M A_i(\rho)]\le\gamma\operatorname{Tr}[M A_i(\sigma)]+\delta$ for all qubit states $\rho,\sigma$ and all effects $M$;
--   2. $r_j<\infty$ for every $j\ne i$, where $r_j$ is the pure-privacy factor of $A_j$, the smallest $\gamma\ge1$ with $\Delta_j(\gamma)=0$.
--
--   Put $G_i=\prod_{j\ne i}g(r_j)$ with $g(r)=\max\{1,(2r-1)/3\}$, and
--   $$\gamma'=\frac{\gamma G_i}{1+(G_i-1)\delta},\qquad \delta'=\frac{G_i\delta}{1+(G_i-1)\delta}.$$
--   Then for every ordered pair of states $\rho,\sigma$ on $(\mathbb C^2)^{\otimes n}$ with $\operatorname{Tr}_i\rho=\operatorname{Tr}_i\sigma$ and every effect $M$ on the output,
--   $$\operatorname{Tr}[M A(\rho)]\le\gamma'\operatorname{Tr}[M A(\sigma)]+\delta'.$$
--   In particular $A$ is $(\log\gamma',\delta')$-QDP at register $i$ against unrestricted measurements: $\Delta^{\mathrm{ALL}}_{A,i}(\gamma')\le\delta'$.
--
--   Only the unchanged channels need finite pure-privacy factors; the changed channel may be only approximately private. When every $r_j\le2$ for $j\neq i$, $G_i=1$ and the bound is the maximum rule at register $i$ for unrestricted observers.
--
--   Differences from the source:
--
--   - generalization: γ ≥ 1 (Definition 2.3) → every real γ > 0; reason: log γ needs only γ > 0 and the proof uses only γ ≥ 0; the case γ ≥ 1 is an instance
--   - encoding: A_i is (log γ, δ)-QDP (a single-register channel) → ∀ qubit states ρ σ and effects M, effectProb M (A_i ρ) ≤ γ · effectProb M (A_i σ) + δ; reason: Definition 2.2 for a single register, where every pair of states is neighboring (§2.1)
--   - encoding: r_j < ∞ for all j ≠ i, r_j the smallest γ with Δ_j(γ) = 0 → hypothesis ∃ γ₀ ≥ 1 with standaloneProfile (A j) γ₀ = 0; r_j = pureFactor (A j) = sInf {γ ≥ 1 | standaloneProfile (A j) γ = 0}; reason: the hypothesis makes the set nonempty, so the infimum is the source value; the bound γ ≥ 1 excludes nothing, since M = I gives Δ_j(γ) ≥ 1 − γ > 0 for γ < 1
--   - encoding: A is (log γ′, δ′)-QDP at register i against unrestricted measurements; the bound holds for every ordered pair with Tr_i ρ = Tr_i σ → conjunct 1: the inequality for every ordered pair of states with traceLeft (splitAt i ρ) = traceLeft (splitAt i σ) and every effect M; conjunct 2: profileAt (allEvents n 2) (tensorChannel A) i γ′ ≤ δ′; reason: both sentences of the theorem, stated literally; ALL is the set of all effects
--   - encoding: Tr[M A(ρ)] → effectProb M (A ρ), the real part of the trace; reason: the trace of an effect against a state is real
-- source:
--   Ji Guan, Yecheng Qin, Parallel Composition of Quantum Differential Privacy: The Role of Measurement Restrictions, STOC 2027 submission #1640 (October 2026), source.pdf SHA-256 da23c8347251683a16df4c61de3fa1604211cdbf34d757a7a45feb0efd54c694, Theorem 5.5 (printed p. 25 / PDF p. 26), proof printed pp. 25–26 / PDF pp. 26–27; setting §2.5 (printed p. 14 / PDF p. 15), Definition 2.2 (printed p. 13 / PDF p. 14), §2.4 eq. (7) (printed p. 14 / PDF p. 15)

import Definitions.Def_GuanQinQDP_Restricted_Supplement_Model
import Definitions.Def_GuanQinQDP_Restricted_Measurements
open QAlgorithms GuanQinQDP.Restricted WildeQIT.EntBreaking
open scoped Matrix ComplexOrder

namespace GuanQinQDP.Restricted.Supplement

/-- Theorem 5.5 (Unrestricted approximate composition), Guan–Qin, STOC 2027 submission #1640,
printed p. 25 / PDF p. 26, in the setting of §2.5 (printed p. 14 / PDF p. 15):
`A = ⨂_{j=1}^n A_j` with every `A_j : M₂ → M₂` a qubit channel, on arbitrary (possibly
entangled) inputs.

Fix a register `i`. Suppose `A_i` is (log γ, δ)-QDP on its own (all pairs of qubit input
states, all effects: `Tr[M A_i(ρ)] ≤ γ Tr[M A_i(σ)] + δ`), and `r_j < ∞` for every `j ≠ i`
(some `γ₀ ≥ 1` has zero standalone profile). With `G_i = ∏_{j ≠ i} g(r_j)`,
`γ' = γ G_i / (1 + (G_i − 1) δ)` and `δ' = G_i δ / (1 + (G_i − 1) δ)`:

1. for every ordered pair of states `ρ, σ` with `Tr_i ρ = Tr_i σ` and every effect `M` on the
   output, `Tr[M A(ρ)] ≤ γ' Tr[M A(σ)] + δ'`;
2. in particular `A` is (log γ', δ')-QDP at register `i` against unrestricted measurements:
   `Δ^ALL_{A,i}(γ') ≤ δ'`. -/
theorem unrestricted_composition {n : ℕ}
    (A : Fin n → (Matrix Qubit Qubit ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ))
    (hA : ∀ j, IsQuantumChannel (A j)) (i : Fin n) (γ δ : ℝ) (hγ : 0 < γ)
    (hpriv : ∀ ρ σ M : Matrix Qubit Qubit ℂ, IsDensityMatrix ρ → IsDensityMatrix σ → IsEffect M →
      effectProb M (A i ρ) ≤ γ * effectProb M (A i σ) + δ)
    (hfin : ∀ j, j ≠ i → ∃ γ₀ : ℝ, 1 ≤ γ₀ ∧ standaloneProfile ⇑(A j) γ₀ = 0) :
    (∀ ρ σ : Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ,
      IsDensityMatrix ρ → IsDensityMatrix σ → traceLeft (splitAt i ρ) = traceLeft (splitAt i σ) →
        ∀ M : Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ, IsEffect M →
          effectProb M (tensorChannel A ρ) ≤
            γ * compCost A i / (1 + (compCost A i - 1) * δ) * effectProb M (tensorChannel A σ) +
              compCost A i * δ / (1 + (compCost A i - 1) * δ)) ∧
    profileAt (allEvents n 2) (tensorChannel A) i
        (γ * compCost A i / (1 + (compCost A i - 1) * δ)) ≤
      compCost A i * δ / (1 + (compCost A i - 1) * δ) := by sorry

end GuanQinQDP.Restricted.Supplement
