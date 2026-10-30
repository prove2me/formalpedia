-- Prove2me | Theorems.Thm_HofmannStreicher1994_semantic_counterexample
-- name    : HofmannStreicher1994.semantic_counterexample
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-29T06:17:50.776995+00:00
-- url     : https://prove2.me/theorems/ad7a0a1e-e77b-4fde-912d-476e3a1e1676
-- title:
--   Section 3: The total universe family fails semantic UIP
-- statement:
--   Let $T$ be the categorical disjoint union of all groupoids whose object and arrow types lie in Lean's base universe. Both semantic UIP and its diagonal version fail for $T$: it is false that every two arrows with common endpoints are connected in the discrete identity groupoid, and it is false that every endomorphism is connected to the identity. The one-object groupoid of permutations of a two-element set supplies the nonidentity loop. This is a semantic counterexample, not yet syntactic underivability.
-- source:
--   Hofmann and Streicher, A Groupoid Model Refutes Uniqueness of Identity Proofs, author manuscript dated 21 March 1994, https://www.dcs.ed.ac.uk/home/mxh/SH.dvi.gz; LICS 1994, https://doi.org/10.1109/LICS.1994.316071. Section 3, manuscript p. 7, nontrivial endomorphism argument for the total universe family.

import Definitions.Def_HofmannStreicher1994_Groupoids

namespace HofmannStreicher1994

theorem semantic_counterexample :
    ¬ SemanticUIP UniverseTotal.{0} ∧ ¬ SemanticBasedUIP UniverseTotal.{0} := by sorry

end HofmannStreicher1994
