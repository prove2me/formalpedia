-- Prove2me | Theorems.Thm_KServerConj_one_server_cost_eq_opt
-- name    : KServerConj.one_server_cost_eq_opt
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T03:41:57.046703+00:00
-- url     : https://prove2.me/theorems/86ece941-6750-401d-83f5-0d9a7293f0b8
-- title:
--   Every one-server serving schedule has optimal cost
-- statement:
--   Let $(M,d)$ be any pseudometric space, let $C_0$ be a singleton initial configuration, and let $r_1,\ldots,r_T$ be requests. Every serving schedule $C_0,C_1,\ldots,C_T$ with exactly one server satisfies
--
--   $$
--   \sum_{t=1}^T D(C_{t-1},C_t)=\operatorname{OPT}_1(C_0;r_1,\ldots,r_T).
--   $$
--
--   The service condition forces $C_t=\{r_t\}$ at every request time. The result therefore applies to every offline serving schedule as well as every Work Function Algorithm trajectory, on finite or infinite spaces.
-- source:
--   Elementary consequence of the serving-schedule definition for k=1, used for the one-server case of Coester–Koutsoupias–Zbysiński, The k-server conjecture is true, arXiv:2609.15979, Section 1.1 and Theorem 1.3 (printed p.2, PDF p.3).

import Definitions.Def_KServerConj_confDist
import Definitions.Def_KServerConj_workFn
import Definitions.Def_KServerConj_IsWFATraj
import Definitions.Def_KServerConj_opt
import Definitions.Def_KServerConj_cl

theorem KServerConj.one_server_cost_eq_opt {M : Type*} [PseudoMetricSpace M]
    (C₀ : Finset M) (hC₀ : C₀.card = 1) (r : ℕ → M) (T : ℕ)
    (C : ℕ → Finset M) (hC : KServerConj.IsSchedule 1 C₀ r T C) :
    KServerConj.wfaCost C T = KServerConj.opt 1 C₀ r T := by sorry
