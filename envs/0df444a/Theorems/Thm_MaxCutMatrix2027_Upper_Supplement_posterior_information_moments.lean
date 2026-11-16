-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_Supplement_posterior_information_moments
-- name    : MaxCutMatrix2027.Upper.Supplement.posterior_information_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:11:10.421531+00:00
-- url     : https://prove2.me/theorems/716a9047-20d8-4fad-a8d4-debc0ef782cd
-- title:
--   Lemma 7.4 — Posterior information moments
-- statement:
--   Let $n\ge2$, $0<\varepsilon\le1/160$, $\rho=40\varepsilon$, and fix a deterministic adaptive algorithm that always makes exactly $q$ distinct pair queries. For every complete transcript $h$ with $\Pr_{D_1^{\mathrm{joint}}}(T=h)>0$ let $\mu_h(s)=\Pr_{D_1^{\mathrm{joint}}}(\Sigma=s\mid T=h)$ and $k(h)=D_{\mathrm{KL}}(\mu_h\|U_n)$ (bits), and set $K=k(T)$. Then, with $\log e=\log_2e$,
--   $$\mathbb E_{D_1^{\mathrm{joint}}}[K]\le\frac23(\log e)\,q\rho^2,\qquad \mathbb E_{D_1^{\mathrm{joint}}}[K^2]\le(\log e)^2\Bigl(4\rho\sqrt q+\frac{16}{3}q\rho^2\Bigr)^2.$$
--
--   These are averages over the random transcript, not pointwise bounds; together with Lemma 7.2 they control the cubic transcript bound.
--
--   Differences from the source:
--   - encoding: vertices (variables) labelled by [n] → Fin n = {0,…,n−1}; reason: relabeling is bijective
--   - encoding: signs and edge indicators in {−1,1} (Y = −1 an edge) → Booleans (true ↦ sign 1; answer true = edge); reason: bijective relabeling; every quantity is transported unchanged
--   - encoding: the distributions D0, D1 and D1^joint of Definition 5.1 → explicit finite mass functions noLaw, yesLaw = ∑_σ yesJoint with yesJoint(σ,G) = 2^{-n} ∏_{u<v} Pr(Y_uv | σ); reason: these are exactly the product laws of Definition 5.1 and Eq. (35)
--   - encoding: a deterministic adaptive algorithm that always makes exactly q distinct queries, with E_t = f_t(T_{t−1}) → a finite decision tree QueryTree whose transcript on every graph has length q and pairwise distinct pairs (ExactlyDistinct q); reason: a decision tree is exactly a family of history-dependent query and output functions; the transcript T = T_q has q steps
--   - encoding: μ_h defined only at histories with Pr(T = h) > 0 → posterior as the ratio Pr(Σ=σ, T=h)/Pr(T=h), equal to 0 at null histories; reason: null histories carry zero weight in every expectation
--   - encoding: expectations under D1^joint of functions of T → ∑ over producible transcripts h of Pr_{D1}(T = h)·K(h); reason: T is a function of the graph, so its law under D1^joint equals its law under D1
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Lemma 7.4, p.34 (PDF p.34); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_Supplement_QueryModel
set_option autoImplicit false
open scoped BigOperators

namespace MaxCutMatrix2027.Upper.Supplement

/-- Lemma 7.4, p.34: first and second moments of `K = D_KL(μ_T ‖ U_n)` under `D₁^joint`, for
every deterministic adaptive tree that always makes exactly `q` distinct queries
(laws of Definition 5.1 with `ρ = 40ε`). -/
theorem posterior_information_moments (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 160) (q : ℕ) (T : QueryTree n) (hT : T.ExactlyDistinct q) :
    let ρ : ℝ := 40 * ε
    let K : List (Sym2 (Fin n) × Bool) → ℝ := fun h => kl (posterior ρ T h) (uniformSigns n)
    ∑ h ∈ transcripts T, transcriptLaw (fun G => yesLaw ρ G) T h * K h ≤
      2 / 3 * log2e * q * ρ ^ 2 ∧
    ∑ h ∈ transcripts T, transcriptLaw (fun G => yesLaw ρ G) T h * K h ^ 2 ≤
      log2e ^ 2 * (4 * ρ * Real.sqrt q + 16 / 3 * q * ρ ^ 2) ^ 2 := by sorry

end MaxCutMatrix2027.Upper.Supplement
