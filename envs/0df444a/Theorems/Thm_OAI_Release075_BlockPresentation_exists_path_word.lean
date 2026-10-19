-- Prove2me | Theorems.Thm_OAI_Release075_BlockPresentation_exists_path_word
-- name    : OAI.Release075.BlockPresentation.exists_path_word
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:36:52.495257+00:00
-- url     : https://prove2.me/theorems/14f6dc96-9db1-4f5a-9237-bc7f1d7209f8
-- title:
--   Discrete Cayley paths are realized by lifted edge words
-- statement:
--   For a block presentation with group $\Gamma$ and its word metric on the Cayley graph of the generators, every discrete path $p$ from $g$ to $h$ is realized by a word $w$ of lifted edges. This word is a path in the lifted complex from $(o,g)$ to $(o,h)$, has length at most $3\,\mathrm{length}(p)$, and has the same tent-form integrals: for all $o',a\in\Gamma$ and $T$,
--   $$
--   \sum_{e\in w}\omega^{\mathrm{lift}}_{o',a,T}(e)=\int_p\omega_{o',a,T}.
--   $$
--
--   This transfers integrals of the tent form from the Cayley graph to words in the triangle complex.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/CayleyPaths.lean#L82-L107

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Chains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CyclicAction
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullChains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_BasedWords
import Definitions.Def_OAI_GroupTheory_Hyperbolic_DiscreteMetric
import Definitions.Def_OAI_GroupTheory_Hyperbolic_ThinTriangles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CayleyMetric
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CayleyPaths

open OAI OAI.Release075 OAI.Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

theorem OAI.Release075.BlockPresentation.exists_path_word {g h : d.GroupType} (p : Discrete.Path d.cayleyMetric g h) :
    ∃ w : List d.LiftedEdge,
      WordPath d.liftedFlip d.liftedTarget (.o,g) (.o,h) w ∧
      w.length ≤ 3*p.length ∧ ∀ (o a : d.GroupType) (T : ℕ),
        (w.map (d.liftedForm o a T)).sum = p.integral (d.cayleyMetric.form o a T) := by sorry
