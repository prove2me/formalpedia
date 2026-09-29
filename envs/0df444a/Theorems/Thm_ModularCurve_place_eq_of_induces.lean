-- Prove2me | Theorems.Thm_ModularCurve_place_eq_of_induces
-- name    : ModularCurve.place_eq_of_induces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/3e5b60a8-b53e-5a31-b5d0-fd9932faeef9
-- title:
--   A Hahn-series embedding induces at most one place
-- statement:
--   Fix a natural number $N \neq 0$ and write $\bar F_N$ for `modularFunctionFieldBar N`, the intermediate field of the Laurent series field $\overline{\mathbb{Q}}((q))$ obtained by adjoining to $\overline{\mathbb{Q}}$ the coefficientwise image of the subfield $\mathbb{Q}(\mathrm{divisorExpansions}\,N) \subseteq \mathbb{Q}((q))$. Let $\psi : \bar F_N \to \mathrm{HahnSeries}\ \mathbb{Q}\ \overline{\mathbb{Q}}$ be an $\overline{\mathbb{Q}}$-algebra homomorphism into the Hahn series over $\overline{\mathbb{Q}}$ with exponents in $\mathbb{Q}$, and let $w, w'$ be places of $\bar F_N$ over $\overline{\mathbb{Q}}$, that is, valuation subrings of $\bar F_N$ containing the image of $\overline{\mathbb{Q}}$, different from the whole field, and which are principal ideal rings. Assume that $\psi$ induces $w$ and that $\psi$ induces $w'$, where `Induces ψ w` means: there is a rational number $g > 0$ such that for every $x \in \bar F_N$ one has $(\mathrm{ord}_w x)\, g = \mathrm{order}(\psi x)$, the order of the Hahn series $\psi x$. The conclusion is $w = w'$: the scaling factors may differ, but the place is unique.
--
--   This is the uniqueness half of the correspondence between embeddings of the level-$N$ modular function field into Hahn series and places of that field, the existence half being a separate statement. It is used in the computation of the orders of vanishing of $j$ and $j - 1728$ at the relevant places, hence in the verification of the Eichler–Selberg/mass-type count of elliptic points, and in [`ModularCurve.emd_holds`](thm.html#ModularCurve.emd_holds).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_place_eq_of_induces.lean

import Definitions.Def_ModularCurve_EMD
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve IsDedekindDomain WithZero

theorem ModularCurve.place_eq_of_induces {N : ℕ} [NeZero N]
    {ψ : ↥(modularFunctionFieldBar N) →ₐ[AlgebraicClosure ℚ] HahnSeries ℚ (AlgebraicClosure ℚ)}
    {w w' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)}
    (h : Induces ψ w) (h' : Induces ψ w') : w = w' := by sorry
