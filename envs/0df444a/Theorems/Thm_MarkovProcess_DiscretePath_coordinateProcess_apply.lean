-- Prove2me | Theorems.Thm_MarkovProcess_DiscretePath_coordinateProcess_apply
-- name    : MarkovProcess.DiscretePath.coordinateProcess_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:32:04.076601+00:00
-- url     : https://prove2.me/theorems/456d7229-d53b-4c56-987a-5c4913ba6c76
-- title:
--   MarkovProcess: coordinateProcess_apply
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_CanonicalDiscretePath_a2b715fb
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Canonical discrete path space

This file records the elementary measurable and filtered structure on the
discrete path space `ℕ → α`.  It does not equip paths with a probability law or
assert any Markov property.

## Main definitions

* `DiscretePath`: the canonical space of `α`-valued discrete paths.
* `DiscretePath.coordinate`: evaluation of a path at one time.
* `DiscretePath.coordinateProcess`: the canonical coordinate process.
* `DiscretePath.canonicalFiltration`: the natural filtration of the coordinate process.
-/

open MeasureTheory
open TopologicalSpace

namespace MarkovProcess



namespace DiscretePath

variable {α : Type*}









section Measurable

variable [MeasurableSpace α]





end Measurable

section NaturalFiltration

variable [TopologicalSpace α]
variable [MetrizableSpace α]
variable [MeasurableSpace α]
variable [BorelSpace α]
variable [SecondCountableTopology α]











end NaturalFiltration

end DiscretePath

end MarkovProcess


open MarkovProcess
open MarkovProcess.DiscretePath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Canonical discrete path space

This file records the elementary measurable and filtered structure on the
discrete path space `ℕ → α`.  It does not equip paths with a probability law or
assert any Markov property.

## Main definitions

* `DiscretePath`: the canonical space of `α`-valued discrete paths.
* `DiscretePath.coordinate`: evaluation of a path at one time.
* `DiscretePath.coordinateProcess`: the canonical coordinate process.
* `DiscretePath.canonicalFiltration`: the natural filtration of the coordinate process.
-/

open MeasureTheory
open TopologicalSpace





variable {α : Type*}







open MarkovProcess.DiscretePath in
@[simp]

theorem MarkovProcess.DiscretePath.coordinateProcess_apply (n : ℕ) (ω : DiscretePath α) :
    coordinateProcess n ω = ω n := by sorry
