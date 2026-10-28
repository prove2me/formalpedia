-- Prove2me | Theorems.Thm_MarkovProcess_PiContinuousMap_exists_coordinateProductTerms_of_mem_coordinateC0Subalgebra
-- name    : MarkovProcess.PiContinuousMap.exists_coordinateProductTerms_of_mem_coordinateC0Subalgebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:46:48.951641+00:00
-- url     : https://prove2.me/theorems/d8eaa22e-6c7d-49fb-9c16-27e54a8035c8
-- title:
--   Finite coordinate-product representation of the C₀ algebra
-- statement:
--   Every member of the coordinate `C₀` algebra is an explicit finite sum of scalar multiples
--   of finite products of one-coordinate `C₀` functions.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/FiniteProductCoordinateNormalForm.lean#L123-L146

import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductCoordinateNormalForm
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductStoneWeierstrass
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
open MarkovProcess MarkovProcess.PiContinuousMap
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Explicit coordinate-product normal forms

This file replaces abstract membership in the coordinate `C₀` algebra by a concrete finite
sum of finite products.  Factors are stored in lists, so the normal form can subsequently be
consumed by recursion (for example, by iterated kernel integration).  The empty factor list is
the constant function `1`; in particular the representation treats constants and an empty
coordinate type without exceptional cases.
-/

open scoped CompactlySupported ZeroAtInfty


variable {I α : Type*} [TopologicalSpace α]

theorem MarkovProcess.PiContinuousMap.exists_coordinateProductTerms_of_mem_coordinateC0Subalgebra
    {h : C(I → α, ℝ)} (hh : h ∈ coordinateC0Subalgebra (I := I) (α := α)) :
    ∃ terms : List (CoordinateProductTerm I α), h = coordinatePolynomial terms := by sorry
