-- Prove2me | Theorems.Thm_GoldreichAffine_Exponential_Supplement_modular_fourier_bound
-- name    : GoldreichAffine.Exponential.Supplement.modular_fourier_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:49:50.919534+00:00
-- url     : https://prove2.me/theorems/14f072f6-7f90-4090-a9e2-7d8c9d59f74e
-- title:
--   Lemma 5 — Fourier bound for modular bit-fixing affine advantage
-- statement:
--   Let $t\ge2$ and $S_0\subseteq\{0,\dots,t-1\}$ with $4\mid t$ and
--
--   $$|S_0\cap2\mathbb Z|=|S_0\cap(2\mathbb Z+1)|=\frac t4. \tag{21}$$
--
--   Let $g=g_{t,S_0}$ be the signed weight profile and $\widehat g_\nu$ its Fourier coefficients. For $b\ge1$ and $0\le r<b$ let $M'$ be any residual of $M_b=\mathsf{MOD}^{t,S_0}_b$ obtained by fixing $r$ inputs, and let $b'=b-r$. For every affine function $f(z)=c\oplus\bigoplus_{j\in A}z_j$ with $A\subseteq[b']$ and $c\in\mathbb F_2$, the agreement probability $q(M',f)=\Pr[M'(U_{b'})=f(U_{b'})]$ satisfies
--
--   $$\Big|q(M',f)-\frac12\Big|\le\frac12\sum_{\substack{0\le\nu<t\\ \nu\ne0,\,t/2}}|\widehat g_\nu|\,\Big|\sin\frac{\pi\nu}t\Big|^{|A|}\Big|\cos\frac{\pi\nu}t\Big|^{b'-|A|}. \tag{22}$$
--
--   Consequently, for every $1\le b'\le b$,
--
--   $$\operatorname{adv}_{b'}(M_b)\le\min\Big\{\frac12,\ \frac{\sqrt{t-2}}2\Big(\cos\frac\pi t\Big)^{b'}\Big\}. \tag{23}$$
--
--   The lemma gives the sufficiency direction of Theorem 3, and (22) is the input to the explicit MOD12 bound of Theorem 6.
--
--   Differences from the source:
--   - encoding: M′ a residual of M_b obtained by fixing r inputs, 0 ≤ r < b, b ≥ 1 → M′ : Predicate (b − r) with IsResidual (published), r < b; reason: the published residual relation fixes exactly b − (b − r) = r inputs; b ≥ 1 follows from r < b
--   - encoding: |S0 ∩ 2Z|, |S0 ∩ (2Z+1)|, S0 ⊆ {0,…,t−1} → (S0.filter Even).card, (S0.filter Odd).card, S0 ⊆ Finset.range t; reason: same sets
--   - encoding: (23) for every 1 ≤ b′ ≤ b with b ≥ 1 → ∀ b b′, 1 ≤ b′ → b′ ≤ b; reason: b ≥ 1 follows from 1 ≤ b′ ≤ b
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, Affine Advantage in Guess-type Attacks on Goldreich’s PRGs: Generalization, Characterization and Countermeasures, STOC 2027 submission #579 (October 2026), PDF SHA-256 c6e5f1bfbc08adde62b9863b4417adb47a894635ef9e887e40be2e7fcd8c0594, pp. 25–26 (PDF pp. 26–27), Lemma 5, Eqs. (21)–(23)

import Definitions.Def_GoldreichAffine_Exponential_Supplement_Modular
open scoped BigOperators
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential.Supplement

/-- Lemma 5, printed pp.25–26 / PDF pp.26–27: both (22) and (23). -/
theorem modular_fourier_bound (t : ℕ) (S0 : Finset ℕ) (ht : 2 ≤ t)
    (hS0 : S0 ⊆ Finset.range t) (h4 : 4 ∣ t)
    (heven : (S0.filter Even).card = t / 4) (hodd : (S0.filter Odd).card = t / 4) :
    (∀ b r : ℕ, r < b → ∀ M' : Predicate (b - r), IsResidual (modPredicate t S0 b) M' →
      ∀ (c : Bool) (A : Finset (Fin (b - r))),
        |uniformAgreement M' (affine c A) - 1 / 2| ≤
          1 / 2 * ∑ ν ∈ (Finset.range t).filter (fun ν => ν ≠ 0 ∧ ν ≠ t / 2),
            ‖fourierCoeff t S0 ν‖ * |Real.sin (Real.pi * (ν : ℝ) / (t : ℝ))| ^ A.card *
              |Real.cos (Real.pi * (ν : ℝ) / (t : ℝ))| ^ (b - r - A.card)) ∧
    (∀ b b' : ℕ, 1 ≤ b' → b' ≤ b →
      advantage (modPredicate t S0 b) b' ≤
        min (1 / 2) (Real.sqrt ((t : ℝ) - 2) / 2 * Real.cos (Real.pi / (t : ℝ)) ^ b')) := by sorry

end GoldreichAffine.Exponential.Supplement
