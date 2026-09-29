-- Prove2me | Theorems.Thm_ModularCurve_B3_exists_variableChange_specialFibre_goodModel
-- name    : ModularCurve.B3.exists_variableChange_specialFibre_goodModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/e52cc5c7-a321-5dde-8043-e54162cec3f8
-- title:
--   Special fibre of the good model is ofJ j₀ up to coordinate change
-- statement:
--   Let $\bar{\mathbb Q}$ denote `Qbar`, the algebraic closure of $\mathbb Q$, and let $j_0 \in \bar{\mathbb Q}$ be arbitrary (no hypothesis on $j_0$ is imposed; in particular the values $0$ and $1728$ are allowed). Over the coefficient field $H$ one forms `nearCurve j₀`, which is Mathlib's standard Weierstrass model `WeierstrassCurve.ofJ` evaluated at `jNear j₀`, and then `goodModel j₀`, the translate of `nearCurve j₀` by the admissible change of coordinates `scaleVC j₀`; the latter is the identity change unless $j_0 = 0$, in which case it is $\bigl(u,r,s,t\bigr) = \bigl(\mathrm{sU}(2/12),\,-(\mathrm{jNear}\,0 - 1728)^2/12,\,-(\mathrm{jNear}\,0 - 1728)/2,\,(\mathrm{jNear}\,0-1728)^3/24\bigr)$, or $j_0 = 1728$, in which case it is $\bigl(\mathrm{sU}(9/12),0,0,0\bigr)$. The Weierstrass curve `specialFibre (goodModel j₀)` over $\bar{\mathbb Q}$ is the one whose five coefficients $a_1,a_2,a_3,a_4,a_6$ are the index-$0$ coefficients of the corresponding coefficients of `goodModel j₀`. The assertion is that there exists a change of coordinates $C \in$ `VariableChange Qbar` whose action on this special fibre gives exactly `WeierstrassCurve.ofJ j₀`, the standard Weierstrass curve over $\bar{\mathbb Q}$ with $j$-invariant $j_0$. No uniqueness of $C$ is claimed, and no ellipticity or nonsingularity statement is part of the conclusion.
--
--   This records that the special fibre of the chosen integral model at $j_0$ is, after an admissible change of coordinates over the algebraically closed residue field, the standard model with $j$-invariant $j_0$ — an instance of the classical fact that two elliptic curves over a separably closed field with the same $j$-invariant are isomorphic. It is the normalisation used when comparing torsion on the generic fibre with torsion on the special fibre, where the residual ambiguity of $C$ by the automorphism group of `WeierstrassCurve.ofJ j₀` is what an equivariance statement must control.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_B3_exists_variableChange_specialFibre_goodModel.lean

import Definitions.Def_ModularCurve_SpecialisationVocab
import Definitions.Def_ModularCurve_TatePoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve
open ModularCurve.TatePoint

theorem ModularCurve.B3.exists_variableChange_specialFibre_goodModel (j₀ : Qbar) :
    ∃ C : VariableChange Qbar,
      C • specialFibre (goodModel j₀) = WeierstrassCurve.ofJ j₀ := by sorry
