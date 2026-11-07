-- Prove2me | Theorems.Thm_HeilmanMax3Cut_dimension_reduction
-- name    : HeilmanMax3Cut.dimension_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:12.32608+00:00
-- url     : https://prove2.me/theorems/f04e9a0b-0e9e-48d5-976e-23f391f6d273
-- title:
--   p.21, $M_m=M_2$ — bilinear dimension reduction ([Hei22])
-- statement:
--   For every $\sigma\in(0,1/2]$ and every $m\ge2$, $M_m=M_2$, where $M_m$ is the infimum of $Q^{(m)}_\sigma(A,B)$ over pairs of partitions of $\mathbb R^m$ into three measurable sets with $\gamma_m(A_i)=\gamma_m(B_i)$.
--
--   The paper takes this from the existence of minimizers and the optimal bilinear dimension-reduction theorem for negative correlation, S. Heilman, [Hei22, Lemma 7.3 and Theorem 7.9], together with the cylinder embedding. It reduces Theorem 7.1 to the plane.
--
--   Differences from the source:
--   - encoding: σ = −ρ for ρ ∈ [−1/2, 0) → σ ∈ (0, 1/2]; reason: σ := −ρ (p.21)
--   - encoding: infimum over pairs of partitions → Mbil: infimum over pairs of a.e.-partitions (IsPartition); reason: a null modification changes neither γ_m(Aᵢ) nor Q, and turns an a.e.-partition into an exact one, so the infima coincide
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Section 7, p.21 ("… give M_m = M_2")

import Mathlib
import Definitions.Def_HeilmanMax3Cut_Mbil

namespace HeilmanMax3Cut

/-- **`M_m = M₂`: bilinear dimension reduction.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Section 7, p.21: "Existence of minimizers and
the optimal bilinear dimension-reduction theorem for negative correlation [Hei22, Lemma 7.3 and
Theorem 7.9], which refines the method of Heilman–Tarter [HT21], together with the cylinder
embedding, give `M_m = M₂`." Here `σ = −ρ ∈ (0, 1/2]` and `M_m` is the infimum of
`Q_σ^{(m)}(A, B)` over pairs of partitions of `ℝᵐ` with `γ_m(Aᵢ) = γ_m(Bᵢ)`.

**Formalization Note.** `Mbil m σ` is that infimum over `IsPartition` pairs (a.e. partitions,
which give the same infimum). Stated for every `m ≥ 2`. -/
theorem dimension_reduction :
    ∀ σ ∈ Set.Ioc (0 : ℝ) (1 / 2), ∀ m : ℕ, 2 ≤ m → Mbil m σ = Mbil 2 σ := by sorry

end HeilmanMax3Cut
