-- Prove2me | Theorems.Thm_ModularCurve_natCard_componentGroup_eq_eisensteinNumerator
-- name    : ModularCurve.natCard_componentGroup_eq_eisensteinNumerator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/da39e1f5-a070-5cc6-8261-6588eed888d0
-- title:
--   Order of the component group is the Eisenstein numerator
-- statement:
--   Let $\iota$ be a finite type, let $e \colon \iota \to \mathbb{N}$ be a width function and let $p$ be a natural number with $1 < p$. Assume: every value $e(x)$ is $1$, $2$ or $3$; the set $\{x : e(x) = 2\}$ is a subsingleton and so is $\{x : e(x) = 3\}$ (at most one index of each of these two widths); and the mass formula $\sum_{x} e(x)^{-1} = (p-1)/12$ holds in $\mathbb{Q}$. Write $X =$ `characterLattice ι` for the kernel of the $\mathbb{Z}$-linear degree map `degreeOn ι` on $\iota \to \mathbb{Z}$, and let `gramMap e` be the $\mathbb{Z}$-linear map $X \to \operatorname{Hom}_{\mathbb{Z}}(X,\mathbb{Z})$ obtained by restricting the bilinear pairing `widthPairing e` in both arguments to $X$. Then the cardinality of the component group $\operatorname{Hom}_{\mathbb{Z}}(X,\mathbb{Z}) / \operatorname{range}(\mathtt{gramMap } e)$ equals `eisensteinNumerator p`, that is, the natural number $(p-1)/\gcd(p-1,12)$ (natural subtraction and division).
--
--   This is the combinatorial form of the Mazur–Rapoport computation of the order of the component group of the Néron model of $J_0(p)$ at $p$: the widths $e(x) \in \{1,2,3\}$ are the thicknesses of the crossing points of the two components of the special fibre of $X_0(p)$, the mass formula is Eichler–Deuring, and the answer is the numerator of $(p-1)/12$. It is used by [`ModularCurve.natCard_componentGroup_eq_and_isAddCyclic_of_width_eq_jWidth`](thm.html#ModularCurve.natCard_componentGroup_eq_and_isAddCyclic_of_width_eq_jWidth), which combines it with the cyclicity statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_componentGroup_eq_eisensteinNumerator.lean

import Definitions.Def_ModularCurve_ComponentGroupKirchhoff
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve Finset
namespace ModularCurve
variable {ι : Type*} [Fintype ι]

theorem natCard_componentGroup_eq_eisensteinNumerator
    (e : ι → ℕ) (p : ℕ) (hp : 1 < p)
    (he : ∀ x, e x = 1 ∨ e x = 2 ∨ e x = 3)
    (h2 : ({x | e x = 2} : Set ι).Subsingleton)
    (h3 : ({x | e x = 3} : Set ι).Subsingleton)
    (hmass : ∑ x, ((e x : ℚ))⁻¹ = ((p : ℚ) - 1) / 12) :
    Nat.card (componentGroup e) = eisensteinNumerator p := by sorry
