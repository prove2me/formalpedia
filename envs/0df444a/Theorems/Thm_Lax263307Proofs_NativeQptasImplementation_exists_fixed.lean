-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeQptasImplementation_exists_fixed
-- name    : Lax263307Proofs.NativeQptasImplementation.exists_fixed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T09:17:37.242691+00:00
-- url     : https://prove2.me/theorems/1fcd902c-0f29-40ca-a30d-51b1ea134829
-- title:
--   Uniform native algorithm data for a separator class
-- statement:
--   Let $\mathcal C$ be a hereditary graph class with strongly edge-sublinear separators. There is one fixed native implementation package:
--   $$\operatorname{Nonempty}(\operatorname{Fixed}(\mathcal C)).$$
--   Its finite backend programs and positive resource constants are selected before the graph, weights, accuracy and host width. The package includes the semantic approximation and uniform root-budget bounds.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeQptasImplementation.lean, theorem exists_fixed; Bonnet–Chang, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf, Sections 3–6

import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces

theorem Lax263307Proofs.NativeQptasImplementation.exists_fixed : ∀ (C : Lax263307.GraphClasses.GraphClass),
  Lax263307.GraphClasses.IsHereditary C →
    Lax263307.EdgeSublinearSeparators.HasStronglyEdgeSublinearSeparators C →
      Nonempty (Lax263307Proofs.NativeQptasImplementation.Fixed C) := by sorry
