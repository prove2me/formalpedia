-- Prove2me | Theorems.Thm_OAI_Falconer_profile_contact_interval
-- name    : OAI.Falconer.profile_contact_interval
-- status  : Proved
-- author  : @dangnguyen
-- created : 2026-10-29T19:23:09.457136+00:00
-- url     : https://prove2.me/theorems/9331399e-306e-4021-881d-1242d9fc192d
-- title:
--   A contact interval for Lipschitz profiles (Falconer, Lemma prep:contact)
-- statement:
--   Let $m:\mathbb{R}\to\mathbb{R}$ be $K$-Lipschitz on $[0,1]$ with $m(0)=0$, and suppose $m(u)\ge su$ for every $u\in[0,1]$. If $q<t<s$, then there exist $0<A<B<1$ with $B<2A$ such that
--
--   $$m(w)\ge qw \quad (0\le w\le A),$$
--   $$m(w)-m(A)\ge t(w-A) \quad (A\le w\le B),$$
--   $$m(w)-m(B)\ge q(w-B) \quad (B\le w\le 1).$$
--
--   Only the values of $m$ on $[0,1]$ matter. The paper states the lemma for $m:[0,1]\to\mathbb{R}$ nondecreasing and Lipschitz. The nondecreasing assumption is not needed, so this statement omits it and is slightly stronger than the paper's. It matches the statement of the same lemma in OpenAI's Lean formalization (`OAI.Falconer.profile_contact_interval`).
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, Section 4 (Preparation), Lemma 'A contact interval' (label prep:contact), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Lean statement as in https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Recursion/ProfileContactInterval.lean#L30-L36

import Mathlib
open Set
open scoped NNReal

namespace OAI
namespace Falconer
theorem profile_contact_interval {m : ℝ → ℝ} {K : ℝ≥0} {q t s : ℝ}
    (hm : LipschitzOnWith K m (Icc 0 1)) (hzero : m 0 = 0)
    (hlower : ∀ u ∈ Icc (0:ℝ) 1, s*u ≤ m u) (hqt : q < t) (hts : t < s) :
    ∃ A B : ℝ, 0 < A ∧ A < B ∧ B < 1 ∧ B < 2*A ∧
      (∀ w ∈ Icc 0 A, q*w ≤ m w) ∧
      (∀ w ∈ Icc A B, t*(w-A) ≤ m w-m A) ∧
      (∀ w ∈ Icc B 1, q*(w-B) ≤ m w-m B) := by sorry
end Falconer
end OAI
