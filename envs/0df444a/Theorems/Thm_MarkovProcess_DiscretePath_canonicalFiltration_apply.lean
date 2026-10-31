-- Prove2me | Theorems.Thm_MarkovProcess_DiscretePath_canonicalFiltration_apply
-- name    : MarkovProcess.DiscretePath.canonicalFiltration_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:32:02.226737+00:00
-- url     : https://prove2.me/theorems/a9b4d3be-23d0-4f16-8353-083fed4cda62
-- title:
--   MarkovProcess: canonicalFiltration_apply
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











variable [TopologicalSpace α]
variable [MetrizableSpace α]
variable [MeasurableSpace α]
variable [BorelSpace α]
variable [SecondCountableTopology α]







open MarkovProcess.DiscretePath in

theorem MarkovProcess.DiscretePath.canonicalFiltration_apply (n : ℕ) :
    canonicalFiltration (α := α) n =
      ⨆ k ≤ n, MeasurableSpace.comap (coordinateProcess (α := α) k) inferInstance := by sorry
