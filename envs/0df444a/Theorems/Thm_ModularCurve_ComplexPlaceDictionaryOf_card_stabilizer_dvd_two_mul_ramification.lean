-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_card_stabilizer_dvd_two_mul_ramification
-- name    : ModularCurve.ComplexPlaceDictionaryOf.card_stabilizer_dvd_two_mul_ramification
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/f826c439-086f-5582-b28a-b5b81eb4a478
-- title:
--   Stabiliser order in ±Γ divides twice the ramification
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ containing the translation matrix $T$, let $F_0$ be an intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ (the Laurent series field over $\mathbb{Q}$), and let $F =$ `laurentBaseChange ℂ F₀` be the subfield of $\mathbb{C}((q))$ obtained by adjoining to $\mathbb{C}$ the image of $F_0$ under the coefficientwise embedding $\mathbb{Q}((q)) \to \mathbb{C}((q))$. Let $D$ be a complex place dictionary for $(\Gamma, F_0)$, that is: a map $\tau \mapsto D.\mathrm{pt}(\tau)$ assigning to each point of the upper half plane a place of $F$ over $\mathbb{C}$ (a valuation subring containing the image of $\mathbb{C}$, not the whole field, and a principal ideal ring), a map $\tau \mapsto D.\mathrm{ramification}(\tau)$ of positive natural numbers, invariance $D.\mathrm{pt}(\gamma \cdot \tau) = D.\mathrm{pt}(\tau)$ for $\gamma \in \Gamma$, the description of the valuation subring at $\tau$ as the set of $x \in F$ whose realisation `realizeOf Γ x` is bounded in norm on a punctured neighbourhood of $\tau$, and, for every $\tau$ and every $x \neq 0$ in $F$, the identity $\mathrm{ord}_\tau\big(z \mapsto \mathrm{realizeOf}\,\Gamma\,x\,z\big) = D.\mathrm{ramification}(\tau) \cdot \mathrm{ord}_{D.\mathrm{pt}(\tau)}(x)$ as meromorphic order at $\tau$; here $\mathrm{realizeOf}\,\Gamma\,x$ is the function sending $\tau$ to $g(\tau)/h(\tau)$ for a chosen pair of modular forms $g, h$ of some common weight on $\Gamma$ with $h(\tau) \neq 0$ and $x \cdot \tilde h = \tilde g$ on $q$-expansions, and to $0$ when no such pair exists. Then for every $\tau$ in the upper half plane, the cardinality of the stabiliser of $\tau$ in the subgroup $\Gamma \vee \langle -1 \rangle$ of $\mathrm{SL}_2(\mathbb{Z})$ divides $2\,D.\mathrm{ramification}(\tau)$.
--
--   This is one half of the identification of the ramification index of a complex place dictionary at $\tau$ with half the order of the stabiliser of $\tau$ in $\pm\Gamma$; it requires neither finite index of $\Gamma$ nor any identification of $F_0$. It is used by [`ModularCurve.ComplexPlaceDictionaryOf.two_mul_ramification_eq_card_stabilizer`](thm.html#ModularCurve.ComplexPlaceDictionaryOf.two_mul_ramification_eq_card_stabilizer), where the divisibility is upgraded to the equality $2 e_\tau = \#(\pm\Gamma)_\tau$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_card_stabilizer_dvd_two_mul_ramification.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.ComplexPlaceDictionaryOf.card_stabilizer_dvd_two_mul_ramification
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀) (τ : UpperHalfPlane) :
    Nat.card (MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) ∣
      2 * D.ramification τ := by sorry
