-- Prove2me | Theorems.Thm_HeilmanMax3Cut_eq_132
-- name    : HeilmanMax3Cut.eq_132
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:32:59.634763+00:00
-- url     : https://prove2.me/theorems/00eaee0f-85df-4359-9017-4498e171c29b
-- title:
--   Eq. (132) — circular rearrangement lower bound
-- statement:
--   Fix $0<\sigma\le1/2$. Let $A,B$ be partitions of $\mathbb R^2$ into three measurable sets with $\gamma_2(A_i)=\gamma_2(B_i)$ for all $i$. Let $p_i(r),q_i(r)$ be the normalized angular measures of $A_i,B_i$ on the circle of radius $\sqrt{2r}$, $b=1/3$, $x_i=p_i-b$, $y_i=q_i-b$, and let $\langle\cdot,\cdot\rangle$ be the inner product of $L^2(\nu)$. Then
--
--   $$Q^{(2)}_\sigma(A,B)-Q^{(2)}_\sigma(\Theta,-\Theta)\ \ge\ \sum_{i=1}^3\Bigl(\langle x_i,K_*y_i\rangle+\langle x_i,M_{J_*}x_i\rangle+\langle y_i,M_{J_*}y_i\rangle\Bigr).$$
--
--   This reduces the bilinear inequality (53) to the nonnegativity of a quadratic form on $L^2(\nu)$.
--
--   Differences from the source:
--   - generalization: (132) derived inside the proof of Theorem 7.1 after restricting to 1/43 ≤ σ ≤ 1/2 → every σ ∈ (0, 1/2]; reason: the derivation (rearrangement and integration of (94)) uses no lower bound on σ; on [1/43, 1/2] it is the paper's statement
--   - generalization: Ω (or A, B) a measurable partition of the space into three disjoint sets → IsPartition: measurable cells, almost every point in exactly one cell; reason: every exact partition is one, so the statement specializes to the paper's; Q and γ do not see null sets
--   - encoding: Θ the three 120° sectors; cells i = 1, 2, 3 → Theta = propeller 2 3 (closed sectors sharing null boundary rays); cells Fin 3 = 0, 1, 2; reason: null overlaps do not change Q; the index shift changes no instance
--   - encoding: pᵢ(r) = ∫_{Aᵢ ∩ √(2r)S¹} dx/(2π√(2r)); ⟨·,·⟩ of L²(ν) → angProf A i r (angle-variable Lebesgue measure / 2π); bil and mulForm iterated integrals against ν; reason: the same quantities
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Section 10, Eq. (132), p.37 (p_i, q_i defined after (53), p.21)

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HeilmanMax3Cut_Qstab
import Definitions.Def_HeilmanMax3Cut_Theta
import Definitions.Def_HeilmanMax3Cut_negP
import Definitions.Def_HeilmanMax3Cut_angProf
import Definitions.Def_HeilmanMax3Cut_Kst
import Definitions.Def_HeilmanMax3Cut_Jst
import Definitions.Def_HeilmanMax3Cut_bil
import Definitions.Def_HeilmanMax3Cut_mulForm
open MeasureTheory OAI.GaussianPropeller

namespace HeilmanMax3Cut

/-- **Eq. (132): circular rearrangement plus integration of (94).** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Section 10, Eq. (132),
p.37: "Recall that `xᵢ := pᵢ − b`, `yᵢ := qᵢ − b`, and `pᵢ, qᵢ : (0, ∞) → [0, 1]` are defined after
(53) … Circular rearrangement with (105) gives
`Q_σ^{(2)}(A, B) − Q_σ^{(2)}(Θ, −Θ) ≥ ∑_{i=1}^3 (⟨xᵢ, K_* yᵢ⟩ + ⟨xᵢ, M_{J_*} xᵢ⟩ + ⟨yᵢ, M_{J_*} yᵢ⟩)`
with `K_*` defined in (104)." Here `A, B` are partitions of `ℝ²` with `γ₂(Aᵢ) = γ₂(Bᵢ)` (the setting
of (53)), `pᵢ(r), qᵢ(r)` are the normalized angular measures of `Aᵢ, Bᵢ` on the circle of radius
`√(2r)`, and `b = 1/3`.

**Formalization Note.** Stated for every `σ ∈ (0, 1/2]` (the paper derives it inside the proof of
Theorem 7.1 after restricting to `1/43 ≤ σ`, a restriction its derivation does not use).
Partitions are `IsPartition` (a.e.); `Θ` is `propeller 2 3`; cells are `Fin 3`. -/
theorem eq_132 (σ : ℝ) (hσ : σ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (A B : Fin 3 → Set (Space 2))
    (hA : IsPartition A) (hB : IsPartition B) (hAB : ∀ i, gaussian 2 (A i) = gaussian 2 (B i)) :
    ∑ i, (bil (Kst σ) (fun r => angProf A i r - 1 / 3) (fun r => angProf B i r - 1 / 3) +
        mulForm (Jst σ) (fun r => angProf A i r - 1 / 3) +
        mulForm (Jst σ) (fun r => angProf B i r - 1 / 3)) ≤
      Qstab 2 σ A B - Qstab 2 σ Theta (negP Theta) := by sorry

end HeilmanMax3Cut
