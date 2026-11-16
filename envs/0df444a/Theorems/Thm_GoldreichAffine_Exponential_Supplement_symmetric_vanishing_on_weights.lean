-- Prove2me | Theorems.Thm_GoldreichAffine_Exponential_Supplement_symmetric_vanishing_on_weights
-- name    : GoldreichAffine.Exponential.Supplement.symmetric_vanishing_on_weights
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:52:45.838338+00:00
-- url     : https://prove2.me/theorems/b9b16b14-cb4f-4952-a788-3bc8130260bf
-- title:
--   Lemma 9 — a symmetric polynomial of degree ≤ e vanishing on $e+1$ weights $r_0+3i$ is zero
-- statement:
--   Let $H$ be a symmetric Boolean polynomial on $d$ variables with algebraic degree at most $e$. Let $r_0\in\{0,1,2\}$ and suppose $r_0+3e\le d$. If
--
--   $$H(z)=0\quad\text{whenever}\quad\|z\|\in\{r_0,\,r_0+3,\,\dots,\,r_0+3e\},$$
--
--   then $H\equiv0$.
--
--   The lemma is the vanishing principle behind the algebraic immunity bound of Lemma 10.
--
--   Differences from the source:
--   - encoding: a symmetric Boolean polynomial H on d variables of degree at most e → H : Word d → Bool, IsSymmetric H, algebraicDegree H ≤ e; reason: a Boolean polynomial and its Boolean function determine each other (unique ANF); degree is Definition 3
--   - encoding: ‖z‖ ∈ {r0, r0+3, …, r0+3e}, r0 ∈ {0,1,2} → ∃ i ≤ e, weight z = r0 + 3i, with r0 ≤ 2; reason: same set
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, Affine Advantage in Guess-type Attacks on Goldreich’s PRGs: Generalization, Characterization and Countermeasures, STOC 2027 submission #579 (October 2026), PDF SHA-256 c6e5f1bfbc08adde62b9863b4417adb47a894635ef9e887e40be2e7fcd8c0594, p. 32 (PDF p. 33), Lemma 9; proof pp. 32–33 (PDF pp. 33–34)

import Definitions.Def_GoldreichAffine_Exponential_Supplement_Algebraic
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential.Supplement

/-- Lemma 9, printed p.32 / PDF p.33. -/
theorem symmetric_vanishing_on_weights (d e r0 : ℕ) (H : Predicate d) (hsym : IsSymmetric H)
    (hdeg : algebraicDegree H ≤ e) (hr0 : r0 ≤ 2) (hd : r0 + 3 * e ≤ d)
    (hvan : ∀ z : Word d, (∃ i : ℕ, i ≤ e ∧ weight z = r0 + 3 * i) → H z = false) :
    ∀ z : Word d, H z = false := by sorry

end GoldreichAffine.Exponential.Supplement
