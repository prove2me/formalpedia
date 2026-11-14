-- Prove2me | Theorems.Thm_LatticePrepro_eq_zero_of_moment_eq_zero
-- name    : LatticePrepro.eq_zero_of_moment_eq_zero
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:20.487013+00:00
-- url     : https://prove2.me/theorems/8aefcb54-5081-4ba2-8a07-5f09e9310920
-- title:
--   Lemma 4.3 (moment identification) — a function on at most $t$ points whose first $t$ moments vanish is zero
-- statement:
--   Let $\Omega$ be a field, let $g\colon \Omega \to \Omega$ be a finitely supported function, and let $t$ be a natural number with $|\operatorname{supp} g| \le t$. If the moments of $g$ of order less than $t$ all vanish,
--   $$\mathcal M_k(g) = \sum_{\alpha \in \operatorname{supp} g} g(\alpha)\,\alpha^k = 0 \qquad (0 \le k < t),$$
--   then $g = 0$.
--
--   Lemma 4.3 of the paper states, for coefficient functions $f, f'\colon \Omega \to \mathbb{F}_p$ with $|\operatorname{supp}(f - f')| \le t$, that $f = f'$ if and only if $\mathcal M_k(f) = \mathcal M_k(f')$ for $0 \le k < t$. The Lean statement is the nontrivial direction, formulated for the difference $g = f - f'$ and in a slightly more general setting: $g$ may take arbitrary values in $\Omega$ rather than in $\mathbb{F}_p$, and $t = 0$ is allowed.
--
--   This Vandermonde argument is what turns the moment equations of the fixed-verifier system into pointwise identities between coefficient functions in the soundness proof of Theorem 4.6.
--
--   **Formalization Note**: $g$ is a `Finsupp` `Ω →₀ Ω`, $|\operatorname{supp} g|$ is `g.support.card`, and the moment is the `moment` of Definitions 4.1–4.2 with coefficient ring $\Omega$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Lemma 4.3 (\label{lem:scalar-moment-identification}); Lean: LatticePrepro/Moments/Basic.lean, LatticePrepro.eq_zero_of_moment_eq_zero

import Mathlib
import Definitions.Def_LatticePrepro_Moments_Basic

open LatticePrepro
open Finsupp
variable {Ω : Type*} [Field Ω]

theorem LatticePrepro.eq_zero_of_moment_eq_zero (g : Ω →₀ Ω) {t : ℕ} (hs : g.support.card ≤ t)
    (h : ∀ k < t, moment g k = 0) : g = 0 := by sorry
