-- Prove2me | Theorems.Thm_Konigsberg_no_eulerian_circuit
-- name    : Konigsberg.no_eulerian_circuit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:43:42.781214+00:00
-- url     : https://prove2.me/theorems/fa3b5bec-f2b2-5a06-93cb-2750f0a77894
-- title:
--   Konigsberg: no eulerian circuit
-- statement:
--   En particular, no hay circuito euleriano; por el teorema de Euler esto equivale a que
--   algún vértice tiene grado impar.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Konigsberg.lean#L65-L66
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Konigsberg.lean#L65-L66

module
public import Definitions.Def_Euler_Basic
public import Mathlib.Tactic.FinCases
public import Definitions.Def_Euler_Konigsberg
set_option autoImplicit true
@[expose] public section
public section
open Konigsberg

theorem Konigsberg.no_eulerian_circuit : ¬ ∃ u, ∃ p : graph.Walk u u, p.IsEulerian := by sorry
