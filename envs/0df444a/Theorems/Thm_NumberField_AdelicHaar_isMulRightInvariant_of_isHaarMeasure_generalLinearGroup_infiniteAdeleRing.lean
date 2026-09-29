-- Prove2me | Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing
-- name    : NumberField.AdelicHaar.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/ea9c88a5-448c-5a6d-b5b8-6c660405b18c
-- title:
--   Right invariance of Haar measure on GL₂ of the archimedean adeles
-- statement:
--   Let $K$ be a number field, and equip the group $\mathrm{GL}_2$ over the infinite adele ring of $K$, that is $\mathrm{GL}(\mathrm{Fin}\ 2, K\otimes_{\mathbb Q}\mathbb R)=\prod_{w\mid\infty}\mathrm{GL}_2(K_w)$, with a measurable space structure which is the Borel structure of its topology. Let $\mu_a$ be a measure on this group which is a Haar measure in the sense of Mathlib, so left invariant, positive on nonempty open sets and finite on compact sets, and which is moreover regular. The conclusion is that $\mu_a$ is also invariant under right translations: for every $a$ in the group, the pushforward of $\mu_a$ along $x\mapsto xa$ equals $\mu_a$, equivalently $\mu_a(Aa^{-1})=\mu_a(A)$ for all measurable $A$. Thus the statement is the unimodularity of $\mathrm{GL}_2$ of the archimedean adeles, in the form that any regular left Haar measure on it is bi-invariant; no normalisation of $\mu_a$ is imposed.
--
--   This is the unimodularity of $\mathrm{GL}_2(K\otimes_{\mathbb Q}\mathbb R)$, in the form needed to replace left by right translations in integrals over the archimedean factor. It is used in the analysis of the cuspidal spectrum, where archimedean convolutions and norm estimates for cusp forms are rewritten by right substitution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicHaar_isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing.lean

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory NumberField.AdelicLevel NumberField.AdelicHaar
open scoped NNReal

theorem NumberField.AdelicHaar.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    (μa : Measure (GL (Fin 2) (InfiniteAdeleRing K))) [μa.IsHaarMeasure] [μa.Regular] :
    μa.IsMulRightInvariant := by sorry
