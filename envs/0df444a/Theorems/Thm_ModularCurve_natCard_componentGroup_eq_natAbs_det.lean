-- Prove2me | Theorems.Thm_ModularCurve_natCard_componentGroup_eq_natAbs_det
-- name    : ModularCurve.natCard_componentGroup_eq_natAbs_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/a990dc94-84e6-5133-b27c-627a42613805
-- title:
--   Order of the component group as a Gram determinant
-- statement:
--   Fix a finite index type $\iota$, a finite index type $\kappa$ and a width function $e : \iota \to \mathbb{N}$, and assume $e(x) > 0$ for every $x \in \iota$. Here the character lattice $\mathtt{characterLattice}\ \iota$ is the $\mathbb{Z}$-submodule of $\iota \to \mathbb{Z}$ cut out as the kernel of the degree map $\mathtt{degreeOn}\ \iota = \sum_{x : \iota} \mathrm{proj}_x$, i.e. the vectors whose coordinates sum to zero; $\mathtt{gramMap}\ e$ is the linear map from this lattice to its $\mathbb{Z}$-dual obtained by restricting the bilinear pairing $\mathtt{widthPairing}\ e$ in both arguments to the character lattice; and the component group $\mathtt{componentGroup}\ e$ is the quotient of $\mathrm{Hom}_{\mathbb{Z}}(\mathtt{characterLattice}\ \iota, \mathbb{Z})$ by the image of $\mathtt{gramMap}\ e$. Let $c$ be a $\mathbb{Z}$-basis of the character lattice indexed by $\kappa$. The assertion is that the cardinality of $\mathtt{componentGroup}\ e$, as a natural number via $\mathtt{Nat.card}$, equals the absolute value of the determinant of the Gram matrix $\mathtt{gramMatrixOf}\ e\ c$, whose $(i,j)$ entry is $(\mathtt{gramMap}\ e\,(c_i))(c_j)$. Since the left-hand side does not involve $c$, the absolute value of the Gram determinant is independent of the chosen basis.
--
--   This is the order formula for the combinatorial (critical, or Néron) component group attached to a weighted configuration, the counterpart of the matrix–tree computation for a weighted graph; it makes the two formulations of the condition that a prime $p$ not divide the component-group order, namely $p \nmid \#\Phi$ and $p \nmid \det(\mathrm{Gram})$, interchangeable. It is used by [`ModularCurve.natCard_componentGroup_eq_natAbs_det_diffChar`](thm.html#ModularCurve.natCard_componentGroup_eq_natAbs_det_diffChar), which evaluates the determinant in a concrete basis of differences of characters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_componentGroup_eq_natAbs_det.lean

import Definitions.Def_ModularCurve_ComponentGroupOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
namespace ModularCurve
open Module
variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ] {e : ι → ℕ}

theorem natCard_componentGroup_eq_natAbs_det (he : ∀ x, 0 < e x)
    (c : Basis κ ℤ (characterLattice ι)) :
    Nat.card (componentGroup e) = ((gramMatrixOf e ⇑c).det).natAbs := by sorry
