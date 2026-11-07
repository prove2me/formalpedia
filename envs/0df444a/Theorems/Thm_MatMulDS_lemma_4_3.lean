-- Prove2me | Theorems.Thm_MatMulDS_lemma_4_3
-- name    : MatMulDS.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:05:27.269831+00:00
-- url     : https://prove2.me/theorems/d2cdd6f8-9670-4dd7-9d82-e2ba377c2a8b
-- title:
--   Lemma 4.3 — lifting data structures beyond $\alpha$
-- statement:
--   Fix $\alpha\in(0,1)$ with $\omega(1,\alpha,1)=2$, and suppose $\omega(1,s,1)\le2+\rho(s)$ for all $s\ge0$, for a nonnegative function $\rho$ with $\rho(\alpha)=\rho'(\alpha)=0$. Let $\mathcal D_{\mathrm{thin}}$ be a bilinear data structure for $N_{\mathrm{thin}}\times D_{\mathrm{thin}}$ and $D_{\mathrm{thin}}\times N_{\mathrm{thin}}$ matrices, where $D_{\mathrm{thin}}=N_{\mathrm{thin}}^\varepsilon$ for a constant $\varepsilon\in(0,\alpha]$, with
--   $$T_{\mathrm{pre}}\le O(N_{\mathrm{thin}}^{2-\beta_{\mathrm{pre}}}),\qquad T_{\mathrm{query}}\le O(N_{\mathrm{thin}}^{\varepsilon-\beta_{\mathrm{query}}}).$$
--   Then there exist constants $\delta_{\mathrm{imp}},\gamma_{\mathrm{pre}},\gamma_{\mathrm{query}}>0$, depending on $\alpha,\varepsilon,\beta_{\mathrm{pre}},\beta_{\mathrm{query}},\rho$, and a bilinear data structure for $N\times D$ and $D\times N$ matrices, where $D=N^{\alpha+\delta_{\mathrm{imp}}}$, with preprocessing time $O(N^{2-\gamma_{\mathrm{pre}}})$ and query time $O(N^{\alpha-\gamma_{\mathrm{query}}})$.
--
--   **Formalization Note** $\alpha$ is any value with these hypotheses, not necessarily the dual exponent.
--
--   Differences from the source:
--   - generalization: $\rho$ differentiable → $\rho$ differentiable at $\alpha$ only, nonnegative on $[0,\infty)$; reason: the printed proof uses only $\rho(\alpha+\Delta)/\Delta\to0$, p.23; a differentiable $\rho$ is a special case
--   - encoding: $D_{\mathrm{thin}}=N_{\mathrm{thin}}^\varepsilon$, $D=N^{\alpha+\delta_{\mathrm{imp}}}$, "family" for large parameters → $\lceil\cdot\rceil$; uniform families `AdmitsDS` over $N\ge N_0$ and over $N\ge N_1$; reason: §4.2, p.16; a single circuit has no $O(s)$
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Lemma 4.3, pp.20–21 (PDF pp.22–23)

import Mathlib
import Definitions.Def_MatMulDS_omegaExp
import Definitions.Def_MatMulDS_UniformFamily

set_option autoImplicit false

namespace MatMulDS

/-- **Lemma 4.3 (Lifting Data Structures Beyond α), pp.20–21** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256 6c5a1c16…). Fix `α ∈ (0, 1)` with `ω(1, α, 1) = 2`, and suppose
`ω(1, s, 1) ≤ 2 + ρ(s)` for all `s ≥ 0`, for a nonnegative function `ρ`, differentiable at `α`, with `ρ(α) = ρ′(α) = 0`. Let `Dthin` be a bilinear data structure for `Nthin × Dthin` and `Dthin × Nthin`
matrices, where `Dthin = Nthin^ε` for a constant `ε ∈ (0, α]`, with `Tpre ≤ O(Nthin^{2−βpre})` and `Tquery ≤ O(Nthin^{ε−βquery})`. Then there exist constants `δimp, γpre, γquery > 0`, depending on `α, ε, βpre,
βquery, ρ`, such that we can construct a new bilinear data structure for `N × D` and `D × N` matrices, where `D = N^{α+δimp}`, with preprocessing time `O(N^{2−γpre})` and query time `O(N^{α−γquery})`.

**Formalization Note.**
* `α` is any value with these hypotheses (footnote 4, p.20), not the dual exponent.
* The constants `δimp, γpre, γquery` precede the thin family, so they do not depend on it or on its implicit constants, as the lemma says.
* `Dthin` is "really a family" over all sufficiently large `Nthin` (§4.2, p.16), uniform as in Definition 4.1 (p.15); the new structure is a uniform family over all sufficiently large `N`.
* `ρ` is differentiable at `α` only: the printed proof uses only `ρ(α + Δ)/Δ → 0` (p.23). -/
theorem lemma_4_3 (F : Type) [Field F] [CharZero F] [DecidableEq F] (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hω : omegaExp F 1 α 1 = 2) (ρ : ℝ → ℝ) (hρ0 : ∀ s, 0 ≤ s → 0 ≤ ρ s)
    (hρω : ∀ s, 0 ≤ s → omegaExp F 1 s 1 ≤ 2 + ρ s) (hρα : ρ α = 0) (hρ' : HasDerivAt ρ 0 α)
    (ε βpre βquery : ℝ) (hε0 : 0 < ε) (hεα : ε ≤ α) (hβpre : 0 < βpre) (hβquery : 0 < βquery) :
    ∃ δimp γpre γquery : ℝ, 0 < δimp ∧ 0 < γpre ∧ 0 < γquery ∧
      ∀ (N₀ : ℕ) (C₀ : ℝ),
        AdmitsDS F (fun N Dm => 1 ≤ N ∧ N₀ ≤ N ∧ Dm = ⌈(N : ℝ) ^ ε⌉₊)
          (fun N _ => C₀ * (N : ℝ) ^ (2 - βpre)) (fun N _ => C₀ * (N : ℝ) ^ (ε - βquery)) →
        ∃ (N₁ : ℕ) (C : ℝ), 0 < C ∧
          AdmitsDS F (fun N Dm => 1 ≤ N ∧ N₁ ≤ N ∧ Dm = ⌈(N : ℝ) ^ (α + δimp)⌉₊)
            (fun N _ => C * (N : ℝ) ^ (2 - γpre)) (fun N _ => C * (N : ℝ) ^ (α - γquery)) := by sorry

end MatMulDS
