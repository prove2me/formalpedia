-- Prove2me | Theorems.Thm_MathieuM23_m23_card_conjClasses
-- name    : MathieuM23.m23_card_conjClasses
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T21:18:53.310301+00:00
-- url     : https://prove2.me/theorems/6b60e195-ea09-4b25-8b92-611af17019f5
-- title:
--   §3 — $M_{23}$ has 17 conjugacy classes
-- statement:
--   The group $M_{23}$ has exactly $17$ conjugacy classes:
--
--   $$1,\ 2,\ 3,\ 4,\ 5,\ 6,\ 7A,\ 7B,\ 8,\ 11A,\ 11B,\ 14A,\ 14B,\ 15A,\ 15B,\ 23A,\ 23B.$$
--
--   **Formalization Note** Only the number of classes is formalized, not the labelling.
-- source:
--   X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, S. Zhang, *The Mathieu group M23 is a Galois group over Q*, arXiv:2608.08538v1 (2026), https://arxiv.org/abs/2608.08538, p. 4, §3 (list $1,2,3,4,5,6,7A,7B,8,11A,11B,14A,14B,15A,15B,23A,23B$)

import Definitions.Def_MathieuM23_Group

namespace MathieuM23

theorem m23_card_conjClasses : Nat.card (ConjClasses M23) = 17 := by sorry

end MathieuM23
