-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_TreeDistortion_FiniteMass_subgroup_average_spectral_mass
-- name    : OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.subgroup_average_spectral_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:30:42.054706+00:00
-- url     : https://prove2.me/theorems/fd1382ff-9def-4945-b8db-b6187522d5a5
-- title:
--   Averaging the translation multiplier over a subgroup
-- statement:
--   Let $A$ be a finite abelian group, $\widehat A$ its characters, and $H:\widehat A\to[0,\infty)$ a spectral mass. For an element $z$, $|1-\chi(z)|^2$ measures how much $\chi$ sees the translation by $z$; for a $\{0,1\}$-valued $f$ with $H=|\hat f|^2$, $\sum_\chi|1-\chi(z)|^2H(\chi)$ is the average of $|f(x+z)-f(x)|$. Let $G$ be a finite abelian group and $\varphi:G\to A$ a homomorphism. Then
--   $$
--   \frac1{|G|}\sum_{z\in G}\sum_\chi|1-\chi(\varphi z)|^2H(\chi)=2\sum_{\chi:\ \chi\circ\varphi\ne1}H(\chi).
--   $$
--
--   Averaging translations over the image of $\varphi$ captures exactly the characters nontrivial on it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/SparseActivity.lean#L321-L341

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped BigOperators
open Classical

theorem OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.subgroup_average_spectral_mass {A G : Type*}
    [AddCommGroup A] [Fintype A] [AddCommGroup G] [Fintype G]
    (φ : G →+ A) (H : AddChar A ℂ → ℝ) :
    (∑ z : G, ∑ χ : AddChar A ℂ, ‖1 - χ (φ z)‖ ^ 2 * H χ) /
        (Fintype.card G : ℝ) =
      2 * ∑ χ : AddChar A ℂ, if χ.compAddMonoidHom φ = 0 then 0 else H χ := by sorry
