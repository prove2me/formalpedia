-- Prove2me | Theorems.Thm_NumberField_TateGlobal_compactSpace_normOneIdeleClass
-- name    : NumberField.TateGlobal.compactSpace_normOneIdeleClass
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/8e36629f-35be-58e1-9033-5fba7cb56833
-- title:
--   Fujisaki's theorem: compactness of the norm-one idele class group
-- statement:
--   Let $F$ be a number field (a field of characteristic zero, finite-dimensional over $\mathbb{Q}$ in the sense of Mathlib's `NumberField`), and form its adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F` relative to the ring of integers $\mathcal{O}_F$, with its group of units $\mathbb{A}_F^\times$. Two subgroups of $\mathbb{A}_F^\times$ enter. First, [`NumberField.TateGlobal.normOneIdeles F`](def/NumberField_TateGlobalZeta.html#L16) is the kernel of the distributive Haar character of $\mathbb{A}_F$, that is the group of those ideles $u$ whose scaling action on a Haar measure of the additive group $\mathbb{A}_F$ multiplies it by $1$; this is the group $\mathbb{A}_F^1$ of norm-one ideles. Second, [`M4aHerbrand.principalIdeles (𝓞 F) F`](def/M4aHerbrand_IdeleClassVocab.html#L16) is the image of the unit group $F^\times$ under the map induced on units by the structure map $F \to \mathbb{A}_F$, i.e. the diagonally embedded principal ideles. The assertion is that the topological quotient of $\mathbb{A}_F^1$ by the intersection of the principal ideles with $\mathbb{A}_F^1$ (the subgroup `subgroupOf` of $\mathbb{A}_F^1$ cut out by `principalIdeles`) is a compact space.
--
--   This is Fujisaki's compactness theorem, the multiplicative counterpart of the compactness of $\mathbb{A}_F/F$; by the product formula, in the form that principal ideles have trivial distributive Haar character ([`NumberField.AdeleRing.distribHaarChar_algebraMap`](thm.html#NumberField.AdeleRing.distribHaarChar_algebraMap)), the subgroup appearing in the quotient is the whole of $F^\times$, so the statement says that the norm-one idele class group $\mathbb{A}_F^1/F^\times$ is compact. It underlies the finiteness and covering statements for Siegel sets and slabs modulo the centre used in the adelic theory of automorphic forms in this development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_compactSpace_normOneIdeleClass.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField M4aHerbrand

theorem NumberField.TateGlobal.compactSpace_normOneIdeleClass (F : Type) [Field F] [NumberField F] :
    CompactSpace (↥(NumberField.TateGlobal.normOneIdeles F) ⧸
      (principalIdeles (𝓞 F) F).subgroupOf (NumberField.TateGlobal.normOneIdeles F)) := by sorry
