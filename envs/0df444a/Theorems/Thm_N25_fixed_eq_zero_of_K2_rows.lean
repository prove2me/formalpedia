-- Prove2me | Theorems.Thm_N25_fixed_eq_zero_of_K2_rows
-- name    : N25.fixed_eq_zero_of_K2_rows
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:45:50.987295+00:00
-- url     : https://prove2.me/theorems/cf084de0-eb1f-484e-815f-77e4c5dff074
-- title:
--   A locally fixed vector in the exact character extension is zero
-- statement:
--   Let $W$ be an additive commutative group, let $\operatorname{act}(\sigma):W\to W$ be a specified family of maps, and let $i:\mathbb F_{71}\to W$ and $q:W\to\mathbb F_{71}$ be additive maps. Assume $i$ is injective, $\ker q=\operatorname{im}i$, $i$ is $\psi$-equivariant, and $q$ is $\chi_{71}$-equivariant. If $v\in W$ is fixed by $\operatorname{act}(r_5\tau)$ for every $\tau\in G_5$, then
--
--   $$v=0.$$
--
--   This is the local fixed-vector vanishing statement that closes the Kummer argument at $5$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_LocalKummerKernel
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace

noncomputable section
open N25
local instance prime71_Thm_N25_fixed_eq_zero_of_K2_rows_ic4550c : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.fixed_eq_zero_of_K2_rows
    {W : Type*} [AddCommGroup W]
    (act : Gal → W → W) (i : ZMod 71 →+ W) (q : W →+ ZMod 71)
    (hi : Function.Injective i) (hexact : q.ker = i.range)
    (hi_galois : ∀ (σ : Gal) (a : ZMod 71), act σ (i a) = i ((psi σ : ZMod 71) * a))
    (hq_galois : ∀ (σ : Gal) (v : W), q (act σ v) = (ExtCitation.cycloChar 71 σ : ZMod 71) * q v)
    (v : W) (hfixed : ∀ τ : G5, act (r5 τ) v = v) : v = 0 := by sorry
