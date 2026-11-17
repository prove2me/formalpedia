-- Prove2me | Theorems.Thm_OracleStateHSP_Supplement_theorem_3_8
-- name    : OracleStateHSP.Supplement.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:14:09.479091+00:00
-- url     : https://prove2.me/theorems/518dc28e-44ce-4509-886e-de9248e9e4f2
-- title:
--   Theorem 3.8 — Copy-based HSP-SAMPLER with $m = \lceil \frac{2}{\varepsilon}\ln\frac{1}{\tilde\delta}\rceil$ Fourier samples
-- statement:
--   Let $G = \mathbb Z_{M_1} \times \dots \times \mathbb Z_{M_n}$ be a finite abelian group with a unitary representation $R$, and let $|\varphi\rangle$ be a StateHSP instance in the sample model (Definition 1.2) with gap parameter $\varepsilon \in (0, 1]$ and hidden subgroup $H$. Let $S^\perp$ be a finite set generating a subgroup $K^\perp = \langle S^\perp\rangle \le H^\perp$, and let $\tilde\delta \in (0, 1]$.
--
--   **Theorem.** Algorithm 2 implements an $\mathrm{HSP\text{-}SAMPLER}(S^\perp, \tilde\delta)$ using at most
--   $$
--   m = \Big\lceil \frac{2}{\varepsilon} \ln \frac{1}{\tilde\delta} \Big\rceil
--   $$
--   calls to a Fourier sampling routine (each on a fresh copy of $|\varphi\rangle$) and at most $m$ classical membership tests $s^\perp \in \langle S^\perp \rangle$. Explicitly, its output law
--
--   1. is a probability distribution on $\hat G \cup \{\mathrm{END}\}$;
--   2. puts probability $1$ on END if $K^\perp = H^\perp$;
--   3. if $K^\perp < H^\perp$, gives positive probability only to END and to elements of $H^\perp \setminus K^\perp$, and outputs an element of $H^\perp \setminus K^\perp$ with probability at least $1 - \tilde\delta$.
--
--   Combined with Algorithm 1 at $\tilde\delta = 1/2$, this sampler gives the $O\big((\log|G/H| + \log\frac1\delta)/\varepsilon\big)$ copy complexity of abelian StateHSP.
--
--   **Formalization Note** The output law is defined from $m$ independent draws from the Born distribution of eq. (24), the output being the first draw outside $\langle S^\perp\rangle$, or END. $\ln$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: an abelian group G (eq. (10)) and its dual → CycProd n M with every M l ≥ 1; characters by eq. (11); reason: covers every finite abelian group up to isomorphism
--   - encoding: calls to a Fourier sampling routine consuming one copy each, and classical membership tests → the output law of Algorithm 2 built from m i.i.d. draws from the Born distribution P of eq. (24), with one membership test per draw; reason: this is what the algorithm does with m copies; P is defined by the Born rule, not by eq. (25)
--   - reading: Algorithm 2 implements an HSP-SAMPLER(S⊥, δ̃) (Definition 3.1, stated for δ̃ ∈ (0,1)) → the two clauses of Definition 3.1 for δ̃ ∈ (0, 1], plus total probability 1 of the output law; reason: Theorem 3.8 itself allows δ̃ ∈ (0, 1]; "outputs END otherwise" means the remaining probability is END
--   - encoding: K⊥ ≤ H⊥, K⊥ = H⊥, K⊥ < H⊥ → inclusion, equality and strict inclusion of the set ⟨S⊥⟩ in the set H⊥; reason: H⊥ is defined as a set (Definition 2.3)
--   - reading: a unitary representation R : G → U(H) on a Hilbert space H (Definition 1.2) → matrices on EuclideanSpace ℂ ι for a finite basis type ι; reason: the paper's state lives in a quantum register acted on by the controlled representation U_R = Σ_g |g⟩⟨g| ⊗ R(g) of the Fourier sampling circuit (eq. (22)), i.e. a finite-dimensional register; the published IsUnitaryRep of the base mission uses the same encoding
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Theorem 3.8, p.25; Algorithm 2, p.25; eq. (24), p.22

import Mathlib
import Definitions.Def_OracleStateHSP_Supplement_IsStateHSPSampleInstance
import Definitions.Def_OracleStateHSP_Supplement_perp
import Definitions.Def_OracleStateHSP_Supplement_alg2Law

namespace OracleStateHSP

namespace Supplement

/-- **Theorem 3.8 (Copy-based HSP-SAMPLER)** (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, Theorem 3.8, p.25; Algorithm 2, p.25).
Let `|φ⟩` be an abelian StateHSP instance in the sample model (Definition 1.2) over
`G = Z_(M_1) × ⋯ × Z_(M_n)` for the unitary representation `R`, with gap `ε ∈ (0, 1]` and hidden
subgroup `H`. Let `S⊥` be a finite set generating `K⊥ = ⟨S⊥⟩ ≤ H⊥`, and `δ̃ ∈ (0, 1]`. Then the
output law of Algorithm 2, which makes `m = ⌈(2/ε) ln(1/δ̃)⌉` i.i.d. Fourier-sampling draws (one copy
each) and one membership test `s⊥ ∈ ⟨S⊥⟩` per draw, is an HSP-SAMPLER(`S⊥`, `δ̃`):

1. it is a probability distribution on `Ĝ ∪ {END}`;
2. if `K⊥ = H⊥`, it outputs END with probability `1`;
3. if `K⊥ < H⊥`, every output of positive probability other than END lies in `H⊥ \ K⊥`, and
   such an output occurs with probability at least `1 − δ̃`.

**Formalization Note.** `ln` is `Real.log`; the budget `m` and the per-draw test are built into
`alg2Law`. `K⊥ ≤ H⊥` and `K⊥ = H⊥` compare `⟨S⊥⟩` with the set `H⊥` (`perp`). -/
theorem theorem_3_8 {n : ℕ} {M : Fin n → ℕ} [∀ l, NeZero (M l)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : CycProd n M → Matrix ι ι ℂ) (φ : EuclideanSpace ℂ ι) (H : AddSubgroup (CycProd n M))
    (ε : ℝ) (hinst : IsStateHSPSampleInstance R φ H ε)
    (S : Finset (CycProd n M))
    (hS : ((AddSubgroup.closure (S : Set (CycProd n M)) : AddSubgroup (CycProd n M)) : Set (CycProd n M)) ⊆
      perp (H : Set (CycProd n M)))
    (δt : ℝ) (hδ0 : 0 < δt) (hδ1 : δt ≤ 1) :
    (∑ o, alg2Law R φ S ε δt o = 1) ∧
    ((((AddSubgroup.closure (S : Set (CycProd n M)) : AddSubgroup (CycProd n M)) : Set (CycProd n M)) =
        perp (H : Set (CycProd n M))) → alg2Law R φ S ε δt none = 1) ∧
    ((((AddSubgroup.closure (S : Set (CycProd n M)) : AddSubgroup (CycProd n M)) : Set (CycProd n M)) ≠
        perp (H : Set (CycProd n M))) →
      (∀ lam, alg2Law R φ S ε δt (some lam) ≠ 0 →
        lam ∈ perp (H : Set (CycProd n M)) ∧
          lam ∉ AddSubgroup.closure (S : Set (CycProd n M))) ∧
      1 - δt ≤ ∑ lam, alg2Law R φ S ε δt (some lam)) := by sorry

end Supplement

end OracleStateHSP
