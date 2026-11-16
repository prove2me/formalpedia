-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_Supplement_pair_correlation_kl
-- name    : MaxCutMatrix2027.Upper.Supplement.pair_correlation_kl
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:10:40.839209+00:00
-- url     : https://prove2.me/theorems/adebaab0-a23b-40ac-935c-dd11097c8a08
-- title:
--   Lemma 7.2 — Squared pair correlations versus KL divergence from uniform
-- statement:
--   Let $\mu$ be any probability distribution on $\{-1,1\}^n$ and $k=D_{\mathrm{KL}}(\mu\|U_n)$, measured in bits. Let $E$ be any set of distinct unordered pairs $\{u,v\}$, $u\neq v$, put $r_{uv}=\mathbb E_{\Sigma\sim\mu}[\Sigma_u\Sigma_v]$ and $s=\sum_{\{u,v\}\in E}r_{uv}^2$. Writing $\log e$ for $\log_2 e$,
--   $$s\le e^2\left(2\sqrt{\frac{k}{\log e}}+\frac{k}{\log e}\right)^2\le\frac{6e^2k}{\log e}+\frac{3e^2k^2}{(\log e)^2}.$$
--
--   No balance, symmetry or positivity assumption is made on $\mu$. Applied to the posterior of the hidden partition given a transcript, this bounds the squared terminal predictions of the queried products.
--
--   Differences from the source:
--   - encoding: vertices (variables) labelled by [n] → Fin n = {0,…,n−1}; reason: relabeling is bijective
--   - encoding: signs and edge indicators in {−1,1} (Y = −1 an edge) → Booleans (true ↦ sign 1; answer true = edge); reason: bijective relabeling; every quantity is transported unchanged
--   - encoding: a probability distribution μ on {−1,1}^n → a nonnegative function on Fin n → Bool with total mass 1; reason: a finite probability law is its mass function
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Lemma 7.2, p.32 (PDF p.32); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_Supplement_QueryModel
set_option autoImplicit false
open scoped BigOperators

namespace MaxCutMatrix2027.Upper.Supplement

/-- Lemma 7.2, p.32: every probability law `μ` on `{−1,1}ⁿ` and every set `E` of distinct
unordered pairs; KL in bits. -/
theorem pair_correlation_kl (n : ℕ) (μ : (Fin n → Bool) → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1) (E : Finset (Sym2 (Fin n))) (hE : ∀ e ∈ E, ¬ e.IsDiag) :
    let k : ℝ := kl μ (uniformSigns n)
    let r : Sym2 (Fin n) → ℝ := fun e => ∑ x, μ x * signProd x e
    let s : ℝ := ∑ e ∈ E, r e ^ 2
    s ≤ Real.exp 1 ^ 2 * (2 * Real.sqrt (k / log2e) + k / log2e) ^ 2 ∧
    Real.exp 1 ^ 2 * (2 * Real.sqrt (k / log2e) + k / log2e) ^ 2 ≤
      6 * Real.exp 1 ^ 2 * k / log2e + 3 * Real.exp 1 ^ 2 * k ^ 2 / log2e ^ 2 := by sorry

end MaxCutMatrix2027.Upper.Supplement
