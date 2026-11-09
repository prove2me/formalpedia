-- Prove2me | Theorems.Thm_IntADSat_theorem_1_1
-- name    : IntADSat.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:52:40.992861+00:00
-- url     : https://prove2.me/theorems/62e44aa9-5df2-4daf-a7ce-9930cbf26688
-- title:
--   Theorem 1.1 — random integral AD-saturation: $\Pr[\Lambda_G\neq\mathbb Z^n]\le n^{-3/20+o(1)}$
-- statement:
--   Let $G\sim G(n,1/2)$ be the Erdős–Rényi random graph on the labelled vertex set $[n]$, let $A_G$ be its adjacency matrix, $D_G=\operatorname{diag}(A_Ge)$ its degree matrix and $e=(1,\dots,1)^{\mathsf T}$. Let
--
--   $$
--   \Lambda_G=\mathbb Z\langle A_G,D_G\rangle e=\operatorname{span}_{\mathbb Z}\{w(A_G,D_G)e: w\text{ a word}\}
--   $$
--
--   be the adjacency–degree word lattice (the empty word included). Then
--
--   $$
--   \Pr\big[\mathbb Z\langle A_G,D_G\rangle e\neq\mathbb Z^n\big]\le n^{-3/20+o(1)} .
--   $$
--
--   In particular, $\Lambda_G=\mathbb Z^n$ with probability tending to one: almost every graph generates every vertex indicator from the all-ones vector by integer combinations of adjacency and degree multiplications, without division.
--
--   Differences from the source:
--   - reading: probability at most n^(−3/20+o(1)) → for every δ > 0, eventually probability ≤ n^(−3/20+δ); reason: equivalent to the existence of ε(n) → 0 with bound n^(−3/20+ε(n)); the standard meaning of o(1) in an exponent of an upper bound
--   - reading: Λ_G = ℤⁿ with probability tending to one → Tendsto of Pr[Λ_G = ℤⁿ] to 1; reason: same meaning
--   - encoding: G ∼ G(n, 1/2) on the labelled vertex set [n] → erProb n (1/2) on SimpleGraph (Fin n) (published Erdős–Rényi product weight at edge probability 1/2); reason: same law: every labelled graph has probability 2^(−n(n−1)/2)
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Theorem 1.1, p.1 (PDF 2)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_IntADSat_wordLattice

set_option autoImplicit false

namespace IntADSat

/-- **Theorem 1.1 (Random integral AD-saturation)** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.1 (PDF 2)). Let `G ∼ G(n, 1/2)`. Then
`Pr[ℤ⟨A_G, D_G⟩e ≠ ℤⁿ] ≤ n^{−3/20+o(1)}`. In particular, `Λ_G = ℤⁿ` with probability tending to one.

**Formalization Note** `G(n, 1/2)` is the uniform law on the labelled simple graphs on `Fin n` (the
published Erdős–Rényi probability `erProb` at edge probability `1/2`); `Λ_G` is the integer span of all
word vectors, the empty word included. `n^{−3/20+o(1)}` is read as: for every `δ > 0`, the probability
is at most `n^{−3/20+δ}` for all large `n`. -/
theorem theorem_1_1 :
    (∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in Filter.atTop,
      LPCommunity.SBMRecovery.erProb n (1 / 2) (fun G => wordLattice G ≠ ⊤) ≤ (n : ℝ) ^ (-(3 / 20 : ℝ) + δ)) ∧
    Filter.Tendsto (fun n : ℕ => LPCommunity.SBMRecovery.erProb n (1 / 2) (fun G => wordLattice G = ⊤))
      Filter.atTop (nhds 1) := by sorry

end IntADSat
