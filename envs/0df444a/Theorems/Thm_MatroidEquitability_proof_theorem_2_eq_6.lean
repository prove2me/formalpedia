-- Prove2me | Theorems.Thm_MatroidEquitability_proof_theorem_2_eq_6
-- name    : MatroidEquitability.proof_theorem_2_eq_6
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T06:31:34.971325+00:00
-- url     : https://prove2.me/theorems/8c9d35e6-1247-4323-95c3-21335e55cccd
-- title:
--   Proof of Theorem 2, (6) — $\gamma=\sum\lambda_{B,D}(|B\cap S|-|D\cap S|)$
-- statement:
--   Let $E$ be a finite set, $\mathcal F^\pm$ finite families of subsets of $E$, $u\in[0,1]^E$, $\gamma\in\mathbb R$, and $\lambda\ge 0$ on $\mathcal F^+\times\mathcal F^-$ with $\sum_{B,D}\lambda_{B,D}=1$. Suppose that $u(B)-u(D)=\gamma$ whenever $\lambda_{B,D}>0$, and that $y:=\sum_{B,D}\lambda_{B,D}(\mathbf 1_B-\mathbf 1_D)$ satisfies the sign conditions (5). With $S:=\{e\in E:u_e=1\}$ and $\mathcal H^\pm$ the supports of the marginals of $\lambda$,
--
--   $$
--   \gamma=\sum_{B\in\mathcal H^+,\,D\in\mathcal H^-}\lambda_{B,D}\bigl(u(B)-u(D)\bigr)=u^\top y=y(S)=\sum_{B\in\mathcal H^+,\,D\in\mathcal H^-}\lambda_{B,D}\bigl(|B\cap S|-|D\cap S|\bigr). \tag{6}
--   $$
--
--   The identity turns the value of the program into a count of elements of $S$ in the two families.
--
--   Differences from the source:
--   - generalization: $(u,\gamma)$, $(\lambda,x)$ optimal for the program of the page → only the properties the page uses: $u\in[0,1]^E$, $\lambda\ge 0$, $\sum\lambda=1$, $u(B)-u(D)=\gamma$ on the support of $\lambda$, and (5); reason: optimal solutions have these properties by `proof_theorem_2_eq_5`
--   - encoding: $u^\top y$ → `setWeight (fun e => u e * y e) E`, the sum of $u_ey_e$ over $E$; reason: the same number
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), Proof of Theorem 2, (6), p.9 (PDF p.11)

import Mathlib
import Definitions.Def_MatroidEquitability_setWeight
import Definitions.Def_MatroidEquitability_dualVector
import Definitions.Def_MatroidEquitability_supportPlus

namespace MatroidEquitability

/-- The chain (6) of the proof of Theorem 2: with `S := {e ∈ E : u_e = 1}`,
`γ = Σ_{H⁺×H⁻} λ_{B,D} (u(B) − u(D)) = uᵀy = y(S) = Σ_{H⁺×H⁻} λ_{B,D} (|B ∩ S| − |D ∩ S|)`
(printed p.9 = PDF p.11 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)).

**Formalization Note.** The hypotheses are what the page uses: `u ∈ [0,1]^E`, `λ ≥ 0`, `Σ λ = 1`,
`u(B) − u(D) = γ` when `λ_{B,D} > 0`, and (5). The inner product `uᵀy` is `setWeight (u · y) E`. -/
theorem proof_theorem_2_eq_6 {α : Type*} (E : Set α) (hE : E.Finite) (Fp Fm : Finset (Set α))
    (hFpE : ∀ B ∈ Fp, B ⊆ E) (hFmE : ∀ D ∈ Fm, D ⊆ E) (u : α → ℝ) (γ : ℝ)
    (lam : Set α → Set α → ℝ) (hu : ∀ e ∈ E, 0 ≤ u e ∧ u e ≤ 1)
    (hlam : ∀ B ∈ Fp, ∀ D ∈ Fm, 0 ≤ lam B D) (hsum : ∑ B ∈ Fp, ∑ D ∈ Fm, lam B D = 1)
    (hslack : ∀ B ∈ Fp, ∀ D ∈ Fm, 0 < lam B D → setWeight u B - setWeight u D = γ)
    (h5 : ∀ e ∈ E,
      (u e = 0 → dualVector Fp Fm lam e ≤ 0) ∧
      (0 < u e → u e < 1 → dualVector Fp Fm lam e = 0) ∧
      (u e = 1 → 0 ≤ dualVector Fp Fm lam e))
    (S : Set α) (hS : S = {e ∈ E | u e = 1}) :
    γ = ∑ B ∈ supportPlus Fp Fm lam, ∑ D ∈ supportMinus Fp Fm lam,
        lam B D * (setWeight u B - setWeight u D) ∧
    ∑ B ∈ supportPlus Fp Fm lam, ∑ D ∈ supportMinus Fp Fm lam,
        lam B D * (setWeight u B - setWeight u D) =
      setWeight (fun e => u e * dualVector Fp Fm lam e) E ∧
    setWeight (fun e => u e * dualVector Fp Fm lam e) E = setWeight (dualVector Fp Fm lam) S ∧
    setWeight (dualVector Fp Fm lam) S =
      ∑ B ∈ supportPlus Fp Fm lam, ∑ D ∈ supportMinus Fp Fm lam,
        lam B D * (((B ∩ S).ncard : ℝ) - ((D ∩ S).ncard : ℝ)) := by sorry

end MatroidEquitability
