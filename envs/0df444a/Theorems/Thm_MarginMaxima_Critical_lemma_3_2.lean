-- Prove2me | Theorems.Thm_MarginMaxima_Critical_lemma_3_2
-- name    : MarginMaxima.Critical.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:03:00.924996+00:00
-- url     : https://prove2.me/theorems/8daf74ad-28bb-42b5-b228-d3d67b8d6575
-- title:
--   Lemma 3.2 — the spectral inequality $(1+\tau)\gamma\le\sqrt{\max_{e\in[0,1]}e(1-\tau e)^2}+\tau(4\omega+(2+\gamma)\sqrt{2\omega})$, $\omega=r/m$
-- statement:
--   Let $x_1,\dots,x_m$ ($m\ge1$) be points of the closed unit ball of $\mathbb R^d$ that are $\gamma$-shattered ($\gamma>0$) with witnesses $s_1,\dots,s_m$ by $F^{(d)}_{\max,r}$, and put $\omega=r/m$. Let $\tau\ge0$, with $\tau=1$ if the witnesses are not all zero. Then
--   $$(1+\tau)\gamma\le\sqrt{\max_{e\in[0,1]}e(1-\tau e)^2}+\tau\big(4\omega+(2+\gamma)\sqrt{2\omega}\big),$$
--   and with zero witnesses
--   $$(1+\tau)\gamma\le\sqrt{\max_{e\in[0,1]}e(1-\tau e)^2}+\tau\big(4\omega+2\sqrt{2\omega}\big).$$
--   With $\tau=1$ (maximum $4/27$) and $\tau=4/3$ at zero witnesses (maximum $1/9$) this gives Theorem 1.1(b).
--
--   Differences from the source:
--   - reading: (1+τ)γ ≤ √(max e(1−τe)²) + ℰ with ℰ ≤ τ(4ω + (2+γ)√(2ω)), and ℰ ≤ τ(4ω + 2√(2ω)) at zero witnesses; ℰ is defined only in the proof → the two combined inequalities with ℰ replaced by its bound; reason: the lemma's content does not depend on the auxiliary ℰ; the combined inequality is what Theorem 1.1(b) uses
--   - reading: let τ = 1 if the witnesses are not all zero → hypothesis τ = 1 ∨ s = 0; reason: literal content of the condition
--   - encoding: the setting: m points γ-shattered with witnesses s_i by F^(d)_max,r, ω = r/m → d, r, m : ℕ with 1 ≤ r, 1 ≤ m, 0 < γ; x : Fin m → Ball d; the shattering condition written out with the witness vector s named; ω written (r : ℝ)/m; reason: the paragraph before the lemma (p. 7); γ is a margin, positive throughout the paper; s must be named to state the zero-witness case
--   - encoding: max_{e∈[0,1]} e(1−τe)² → sSup of the image of Set.Icc 0 1; reason: a continuous function on a compact interval: the supremum is attained and equals the maximum
--   - encoding: x ↦ max_{j≤r}⟨u_j, x⟩ on the unit ball of R^d, ∥u_j∥ ≤ 1, labels in {±1} → MaxClass d r: functions on the closed-ball subtype Ball d, ⨆ over j : Fin r of inner ℝ (u j) x, ‖u j‖ ≤ 1; labels Bool read through pm; reason: for r ≥ 1 the supremum over Fin r is the maximum of r reals; pm true = 1, pm false = −1
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 7, Lemma 3.2

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_MarginMaxima_Critical_MaxClass

open BartlettNN.Margin
open scoped ENNReal

namespace MarginMaxima.Critical

theorem lemma_3_2 (d r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m) (γ τ : ℝ) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (x : Fin m → Ball d) (s : Fin m → ℝ)
    (hsh : ∀ b : Fin m → Bool, ∃ f ∈ MaxClass d r, ∀ i, γ ≤ (f (x i) - s i) * pm (b i))
    (hτs : τ = 1 ∨ s = 0) :
    (1 + τ) * γ ≤ Real.sqrt (sSup ((fun e : ℝ => e * (1 - τ * e) ^ 2) '' Set.Icc 0 1)) +
        τ * (4 * ((r : ℝ) / m) + (2 + γ) * Real.sqrt (2 * ((r : ℝ) / m))) ∧
      (s = 0 → (1 + τ) * γ ≤ Real.sqrt (sSup ((fun e : ℝ => e * (1 - τ * e) ^ 2) '' Set.Icc 0 1)) +
        τ * (4 * ((r : ℝ) / m) + 2 * Real.sqrt (2 * ((r : ℝ) / m)))) := by sorry

end MarginMaxima.Critical
