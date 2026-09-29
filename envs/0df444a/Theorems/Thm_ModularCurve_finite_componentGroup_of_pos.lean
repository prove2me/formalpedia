-- Prove2me | Theorems.Thm_ModularCurve_finite_componentGroup_of_pos
-- name    : ModularCurve.finite_componentGroup_of_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/f4e1162b-e440-5551-8ee4-db0d29727eff
-- title:
--   Finiteness of the component group for positive weights
-- statement:
--   Let $\iota$ be a finite type and let $e : \iota \to \mathbb{N}$ be a family of natural numbers with $e(x) > 0$ for every $x$. The ambient lattice is $\iota \to \mathbb{Z}$, and `characterLattice ι` is the kernel of the linear map `degreeOn ι` on it; the form `widthPairing e` restricted in both arguments to this kernel gives the $\mathbb{Z}$-linear map $\mathrm{gram}_e =$ `gramMap e` from `characterLattice ι` to its $\mathbb{Z}$-dual $\operatorname{Hom}_{\mathbb{Z}}(\mathrm{characterLattice}\,\iota, \mathbb{Z})$. The object `componentGroup e` is by definition the quotient of that dual by the image of $\mathrm{gram}_e$, i.e. the cokernel of $\mathrm{gram}_e$. The assertion is that this quotient is a finite type. Nothing is claimed about its order here, and no hypothesis beyond finiteness of $\iota$ and positivity of all the weights $e(x)$ is required; the positivity hypothesis is genuinely needed, since for $\iota$ with two elements and all weights zero the pairing vanishes and the quotient is the infinite group $\operatorname{Hom}_{\mathbb{Z}}(\mathrm{characterLattice}\,\iota, \mathbb{Z}) \cong \mathbb{Z}$.
--
--   This is the finiteness of the combinatorial component group attached to a weighted finite set of crossing points, the group-theoretic shadow of the component group of the Néron model of a curve with split multiplicative-type reduction, the weights $e(x)$ being the thicknesses (widths) at the crossings. It is used in the analysis of Tate modules and torsion of Néron models at primes of bad reduction, for instance by the statements about eigenplanes and torsion lines in Tate modules and by the bound on the order of inertia-invariant torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finite_componentGroup_of_pos.lean

import Definitions.Def_ModularCurve_ComponentGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.finite_componentGroup_of_pos {ι : Type*} [Fintype ι] (e : ι → ℕ)
    (he : ∀ x, 0 < e x) : Finite (componentGroup e) := by sorry
