-- Prove2me | Theorems.Thm_MarkovProcess_exists_factor_succAboveOrderEmb
-- name    : MarkovProcess.exists_factor_succAboveOrderEmb
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:11:53.475288+00:00
-- url     : https://prove2.me/theorems/2fe6be5c-aed3-47fd-85a7-81d274109445
-- title:
--   Factor a finite order embedding through deletion of one point
-- statement:
--   Let $m,n$ be natural numbers with $m \le n$. Every order embedding $e : \operatorname{Fin}(m) \hookrightarrow_o \operatorname{Fin}(n+1)$ factors through the order embedding that skips some point $p \in \operatorname{Fin}(n+1)$. Precisely, there is an order embedding $d : \operatorname{Fin}(m) \hookrightarrow_o \operatorname{Fin}(n)$ whose composition with the skip embedding equals $e$. This is the source theorem used for finite-time reindexing, not a placeholder.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Time/FiniteOrderEmbedding.lean#L23-L63

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Fin.Basic

theorem MarkovProcess.exists_factor_succAboveOrderEmb {m n : ℕ} (e : Fin m ↪o Fin (n + 1)) (h : m ≤ n) :
    ∃ (p : Fin (n + 1)) (d : Fin m ↪o Fin n), d.trans (Fin.succAboveOrderEmb p) = e := by sorry
