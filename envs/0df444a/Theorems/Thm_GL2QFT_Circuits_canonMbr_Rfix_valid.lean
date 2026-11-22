-- Prove2me | Theorems.Thm_GL2QFT_Circuits_canonMbr_Rfix_valid
-- name    : GL2QFT.Circuits.canonMbr_Rfix_valid
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T06:01:06.579774+00:00
-- url     : https://prove2.me/theorems/e0720a56-04b6-4001-addc-72a6d8588e9c
-- title:
--   Admissibility and isometry properties of the canonical Theorem 6.34 stages for $q > 2$
-- statement:
--   For any field instance $D$ with $q > 2$ and any $\gamma \in \mathbb{Z}/(q-1)\mathbb{Z}$:
--
--   1. `canonMbr D γ` satisfies `IsBranchTransform D γ` and `canonRfix D γ` satisfies `IsFixingGate D γ` (with unused set $U = \mathrm{Irr}(\mathrm{GL}_2(\mathbb{F}_q))$).
--
--   2. Because `Bgate D γ` is supported exclusively inside `BranchSrc D`, `canonMbr D γ * Bgate D γ = canonMbrCore D γ * BgateSub D γ`.
--
--   3. All five pre-correction stages (`Dgate`, `FxDag`, `BgateSub`, `canonMbrCore`, `canonRfix`) are exact isometries ($M^\dagger M = I$).
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.5, Definitions 6.16–6.21 & Theorem 6.27 (pp. 49–55)

import Definitions.Def_GL2QFT_Circuits_Leaves

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem canonMbr_Rfix_valid (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) : IsBranchTransform D γ (canonMbr D γ) ∧ IsFixingGate D γ (canonRfix D γ) ∧ canonMbr D γ * Bgate D γ = canonMbrCore D γ * BgateSub D γ ∧ (Dgate D γ).conjTranspose * Dgate D γ = 1 ∧ (FxDag D).conjTranspose * FxDag D = 1 ∧ (BgateSub D γ).conjTranspose * BgateSub D γ = 1 ∧ (canonMbrCore D γ).conjTranspose * canonMbrCore D γ = 1 ∧ (canonRfix D γ).conjTranspose * canonRfix D γ = 1 := by sorry

end Circuits
end GL2QFT
