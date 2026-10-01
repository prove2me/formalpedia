-- Prove2me | Theorems.Thm_HadwigerConj_albar_goncalves
-- name    : HadwigerConj.albar_goncalves
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T23:31:31.218985+00:00
-- url     : https://prove2.me/theorems/452bb462-de03-4c44-9f1a-f4be9a366a5e
-- title:
--   Theorem 2.3 (Albar–Gonçalves): no $K_7$ minor $\Rightarrow$ $8$-colourable; no $K_8$ minor $\Rightarrow$ $10$-colourable
-- statement:
--   Let $G$ be a finite graph.
--
--   1. If $G$ has no $K_7$ minor, then $G$ is $8$-colourable.
--   2. If $G$ has no $K_8$ minor, then $G$ is $10$-colourable.
--
--   These are the best known bounds in the first open cases $\mathrm{HC}(6)$ and $\mathrm{HC}(7)$.
-- source:
--   P. Seymour, "Hadwiger's conjecture" (survey), in: Open Problems in Mathematics, Springer, 2016 (uploaded PDF `paper.pdf`), Theorem 2.3 (p. 4)

import Mathlib
import Definitions.Def_HadwigerConj_Defs

namespace HadwigerConj
theorem albar_goncalves {V : Type} [Finite V] (G : SimpleGraph V) :
    (¬ HasCompleteMinor G 7 → G.Colorable 8) ∧
    (¬ HasCompleteMinor G 8 → G.Colorable 10) := by sorry
end HadwigerConj
