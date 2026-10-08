-- Prove2me | Theorems.Thm_MartOT_Var_gamma_iInter
-- name    : MartOT.Var.gamma_iInter
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:00.017177+00:00
-- url     : https://prove2.me/theorems/161eea91-b88e-4867-9eb6-03082f5a93a5
-- title:
--   Proof of Lemma 1.11, p. 17 — Γ = ⋂ₙ Γₙ is as required
-- statement:
--   Let $c:\mathbb R^2\to\mathbb R$ be a cost and $\pi$ a measure on $\mathbb R^2$. Suppose that for each $n\in\mathbb N$ a Borel set $\Gamma_n$ with $\pi(\mathbb R^2\setminus\Gamma_n)=0$ is given such that every finite measure $\alpha=\sum_{s\in S}w_s\delta_s$ with $S\subseteq\Gamma_n$, $|S|\le n$, satisfies $\int c\,d\alpha\le\int c\,d\alpha'$ for every competitor $\alpha'$. Then $\Gamma=\bigcap_{n\in\mathbb N}\Gamma_n$ is Borel, $\pi(\mathbb R^2\setminus\Gamma)=0$, and
--   $$\int c\,d\alpha\le\int c\,d\alpha'\quad\text{for every competitor }\alpha'\text{ of every finitely supported }\alpha\text{ with }\operatorname{spt}\alpha\subseteq\Gamma .$$
--
--   This is the last step of the proof of the variational lemma.
--
--   **Formalization Note** Finitely supported finite measures are finite weighted sums of Dirac masses, as in the main statement.
-- source:
--   arXiv:1208.1509v2, §3, proof of Lemma 1.11, p. 17 ("Clearly, Γ = ⋂_{n∈N} Γ_n is then as required to establish the lemma.")

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Var

open MeasureTheory

theorem gamma_iInter (c : ℝ → ℝ → ℝ) (π : Measure (ℝ × ℝ)) (Γn : ℕ → Set (ℝ × ℝ))
    (hmeas : ∀ n, MeasurableSet (Γn n)) (hfull : ∀ n, π (Γn n)ᶜ = 0)
    (hopt : ∀ n (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), S.card ≤ n →
      (↑S : Set (ℝ × ℝ)) ⊆ Γn n → ∀ α' : Measure (ℝ × ℝ),
        IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
        cost c (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤ cost c α') :
    MeasurableSet (⋂ n, Γn n) ∧ π (⋂ n, Γn n)ᶜ = 0 ∧
      ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ ⋂ n, Γn n →
        ∀ α' : Measure (ℝ × ℝ),
          IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
          cost c (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤ cost c α' := by sorry

end MartOT.Var
