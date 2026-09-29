-- Prove2me | Theorems.Thm_Module_Flat_ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range
-- name    : Module.Flat.ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/c093f0ed-3f09-5532-b4a7-e89709475980
-- title:
--   Exactness over a local ring from exactness on the residue field
-- statement:
--   Let $R$ be a Noetherian local commutative ring, and let $C : \mathbb{N} \to \mathrm{Type}$ be a family of $R$-modules, each flat over $R$, together with $R$-linear maps $d_i : C_i \to C_{i+1}$ satisfying $d_{i+1} \circ d_i = 0$ for all $i$. Assume the complex is bounded in the sense that there is an $n \in \mathbb{N}$ with $C_i$ subsingleton (a zero module) for all $i \ge n$, and that for every $i$ the quotient of $\ker d_{i+1}$ by the preimage of $\operatorname{range} d_i$ under the inclusion $\ker d_{i+1} \hookrightarrow C_{i+1}$ — that is, the cohomology $H^{i+1}(C)$ — is a finitely generated $R$-module. Assume finally that for every $i$ the base change of the complex to the residue field $\kappa =$ `IsLocalRing.ResidueField R` is exact in the corresponding degree: $\ker(d_{i+1} \otimes_R \kappa) \le \operatorname{range}(d_i \otimes_R \kappa)$. Then two conclusions hold simultaneously: first, $\ker d_{i+1} \le \operatorname{range} d_i$ for every $i$; and second, for every field $K$ in the same universe carrying an $R$-algebra structure and every $i$, $\ker(d_{i+1} \otimes_R K) \le \operatorname{range}(d_i \otimes_R K)$. Note that the indexing makes both conclusions assertions about positive degrees only; no exactness at $C_0$ is claimed.
--
--   This is the local form of upper semicontinuity of fibre cohomology: for a bounded complex of flat modules with finitely generated cohomology over a Noetherian local base, exactness in positive degrees on the closed fibre propagates to the complex itself and to every field-valued fibre. It is used in the study of good reduction of Jacobians, where vanishing of the higher cohomology of the closed fibre of a Čech-type complex is to be spread to all fibres, and it feeds a companion statement producing such vanishing on a basic open neighbourhood over a general Noetherian base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Flat_ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.Flat.ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (hfib : ∀ i : ℕ,
      LinearMap.ker ((d (i + 1)).baseChange (IsLocalRing.ResidueField R)) ≤
        LinearMap.range ((d i).baseChange (IsLocalRing.ResidueField R))) :
    (∀ i : ℕ, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i)) ∧
      ∀ (K : Type u) [Field K] [Algebra R K] (i : ℕ),
        LinearMap.ker ((d (i + 1)).baseChange K) ≤ LinearMap.range ((d i).baseChange K) := by sorry
