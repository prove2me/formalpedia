-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp
-- name    : NumberField.PlaceDecomp.exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/c87d59e8-eced-541d-9953-8cd409c05d62
-- title:
--   Higher units are norms from a prime-degree layer beyond the jump
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois, let $v$ be a nonzero prime of $\mathcal{O}_E$ and $w$ a nonzero prime of $\mathcal{O}_F$ with $w$ lying under $v$ (i.e. $w \cap \mathcal{O}_E = v$). Write $D =$ `decomp E F w` for the decomposition subgroup of $\mathrm{Gal}(F/E)$ attached to the valuation subring of the $w$-adic valuation on $F$, and assume $\ell := \#D$ is prime. Let $t$ be a natural number such that the $t$-th lower ramification group of that valuation subring over $E$ — the inertia subgroup, inside $D$, of the $(t+1)$-st power of the maximal ideal — is all of $D$, while the $(t+1)$-st is trivial; so $t$ is the unique jump. Let $n > t$, and let $a$ be a unit of the completion $E_v$ with $|a| = 1$ and $|a - 1| \le \exp(-n)$. Then there is a unit $b$ of the completion $F_w$ with $|b| = 1$, with $|b - 1| \le \exp(-(t + \ell(n - t)))$ (the subtraction being truncated subtraction of naturals), and such that the finite product $\prod_{\sigma \in D} \sigma \cdot b$, viewed in $F_w$, equals the image of $a$ under the semialgebra map $E_v \to F_w$ induced by $E \to F$ at the place $w$ above $v$.
--
--   This is the arithmetic input for the inclusion half of the filtration theorem of local class field theory: in a totally ramified cyclic layer of prime degree $\ell$ with single ramification jump $t$, the norm map carries the higher unit group of level $\psi(n) = t + \ell(n-t)$ onto that of level $n$ for every $n > t$ (Serre, Corps locaux V). It is used by [`NumberField.PlaceDecomp.exists_forall_upperRamificationGroup_smul_eq_and_finprod_quotient_smul_eq_of_valuation_sub_one_le`](thm.html#NumberField.PlaceDecomp.exists_forall_upperRamificationGroup_smul_eq_and_finprod_quotient_smul_eq_of_valuation_sub_one_le), which climbs the ramification tower one prime-degree layer at a time.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_finprod_smul_eq_of_valuation_sub_one_le_of_jump_lt_of_prime_card_decomp
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)
    (hℓ : (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w)).Prime)
    (t : ℕ)
    (ht : ((w.valuation F).valuationSubring).lowerRamificationGroup E t = ⊤)
    (ht' : ((w.valuation F).valuationSubring).lowerRamificationGroup E (t + 1) = ⊥)
    (n : ℕ) (hn : t < n) (a : (v.adicCompletion E)ˣ)
    (ha1 : Valued.v (a : v.adicCompletion E) = 1)
    (han : Valued.v ((a : v.adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ))) :
    ∃ b : (w.adicCompletion F)ˣ, Valued.v (b : w.adicCompletion F) = 1 ∧
      Valued.v ((b : w.adicCompletion F) - 1) ≤
        WithZero.exp (-((t + Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) * (n - t) : ℕ) : ℤ)) ∧
      (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) : w.adicCompletion F) =
        IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) (a : v.adicCompletion E) := by sorry
