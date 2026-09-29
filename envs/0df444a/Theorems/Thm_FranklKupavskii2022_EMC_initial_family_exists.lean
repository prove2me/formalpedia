-- Prove2me | Theorems.Thm_FranklKupavskii2022_EMC_initial_family_exists
-- name    : FranklKupavskii2022.EMC.initial_family_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:15:51.906966+00:00
-- url     : https://prove2.me/theorems/3f4ae97e-8cee-4129-ae15-76ed24065e13
-- title:
--   Lemma 3: shifting to an initial family keeps the size and does not increase $\nu$
-- statement:
--   Let $m,k\ge0$. For every family $\tilde{\mathcal F}\subseteq\binom{[m]}{k}$ there is an initial family $\mathcal F\subseteq\binom{[m]}{k}$ with
--
--   $$
--   |\mathcal F|=|\tilde{\mathcal F}|\quad\text{and}\quad \nu(\mathcal F)\le\nu(\tilde{\mathcal F}).
--   $$
--
--   Consequently, in the Erdős matching problem one may restrict attention to initial (shifted) families. The lemma is due to Frankl (1987) and is quoted in the paper without proof.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Lemma 3, p. 3 (citing [13] Frankl 1987)

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
import Definitions.Def_FranklKupavskii2022_EMC_IsInitial

namespace FranklKupavskii2022.EMC

/-- Lemma 3 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 3, citing Frankl 1987 [13]): for every
family `F̃ ⊂ \binom{[m]}{k}` there is an initial family `F ⊂ \binom{[m]}{k}` with `|F| = |F̃|` and
`ν(F) ≤ ν(F̃)`.

**Formalization Note.** `[m] = Finset.Icc 1 m`; "initial" is `IsInitial m k`, whose downward
closure ranges over `k`-subsets of `[m]`. -/
theorem initial_family_exists (m k : ℕ) (Ft : Finset (Finset ℕ))
    (hFt : Ft ⊆ (Finset.Icc 1 m).powersetCard k) :
    ∃ F : Finset (Finset ℕ), F ⊆ (Finset.Icc 1 m).powersetCard k ∧ IsInitial m k F ∧
      F.card = Ft.card ∧ matchingNumber F ≤ matchingNumber Ft := by sorry

end FranklKupavskii2022.EMC
