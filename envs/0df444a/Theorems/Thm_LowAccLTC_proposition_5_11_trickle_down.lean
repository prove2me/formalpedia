-- Prove2me | Theorems.Thm_LowAccLTC_proposition_5_11_trickle_down
-- name    : LowAccLTC.proposition_5_11_trickle_down
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:40:20.064996+00:00
-- url     : https://prove2.me/theorems/6cf2a122-9b58-4a7a-a03b-0a5178610403
-- title:
--   Proposition 5.11 (Trickling down) — link agreement testability gives $(\alpha_0-\sqrt\lambda,\rho)$-agreement testability on a $\lambda$-product
-- statement:
--   Let $\alpha_0\le0.005$, let $\rho:\mathbb R_+\to\mathbb R_+$ be non-decreasing with
--   $$\rho(x)+\frac{x}{2\rho(x)}\le0.88\qquad\text{for every }x\in(0,\alpha_0],$$
--   let $\delta\ge0.9$ and $\lambda\ge0$. Let $Y$ be a weighted pure $r$-partite complex of rank $r\ge3$ that is a $\lambda$-product, with local codes $C_{uv}$ on the edges, link codes $C_v=\mathrm{Tan}(Y_v,\{C_{uv}\}_u)$ and global code $C=\mathrm{Tan}(Y,\{C_{uv}\})$. If every edge code $C_{uv}$ has distance at least $\delta$ and every link code $C_v$ is $(\alpha_0,\rho)$-agreement testable w.r.t. the vertex agreement test on $Y_v$, then $C$ is
--   $$(\alpha_0-\sqrt\lambda,\ \rho)\text{-agreement testable}$$
--   w.r.t. the vertex agreement test on $Y$.
--
--   Applied repeatedly to the links of $Y^{\mathcal P}$, it lifts Claim 5.12 to all of $Y^{\mathcal P}$ in the proof of Claim 5.8.
--
--   Differences from the source:
--   - reading: ρ 'monotonically increasing' → ρ non-decreasing on [0, ∞) (MonotoneOn); reason: the paper's usage in Definitions 2.2 and 2.6; the weaker hypothesis gives the stronger theorem
--   - reading: ρ(x) + x/(2ρ(x)) ≤ 0.88 on (0, α₀] → 0 < ρ(x) and ρ(x) + x/(2ρ(x)) ≤ 0.88 on (0, α₀]; reason: the expression divides by ρ(x), which the paper takes as nonzero; with Lean's x/0 = 0, ρ ≡ 0 would satisfy the inequality although the conclusion then fails
--   - reading: 'agreement testable w.r.t. the vertex test' → w.r.t. the vertex agreement test (Definition 5.10) on Y_v and on Y; reason: §7 (p.63) recalls that the test meant is the vertex agreement test
--   - encoding: ρ : ℝ₊ → ℝ₊ → ρ : ℝ → ℝ with ρ ≥ 0 on [0, ∞); reason: only values on [0, ∞) are read
--   - encoding: a pure r-partite simplicial complex with a positive probability measure on its top faces → PartiteComplex: a finite type of top faces with a vertex map vert t i of colour i (colours Fin r, the paper's colour i is i − 1), injective on top faces, and a positive measure μ summing to 1; reason: faces are the subsets of top faces, so this is exactly a pure weighted r-partite complex
--   - encoding: λ-one-sided spectral expansion of the swap walks → the variational form (E g(u)h(w))² ≤ λ² E g² E h² for g of mean 0; reason: equivalent to ‖A_L|_{1⊥}‖ ≤ λ for λ ≥ 0
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Proposition 5.11, p.48 (PDF p.51); restated p.63 (PDF p.66)

import Definitions.Def_LowAccLTC_edgeTanner
import Definitions.Def_LowAccLTC_IsVATestable
import Definitions.Def_LowAccLTC_IsLambdaProduct

namespace LowAccLTC

/-- **Proposition 5.11** (Trickling down for agreement testability; Ben Yaacov–Dikstein–Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs* (manuscript, sha256 04242e17…), p.48 = PDF p.51;
restated p.63).

Let `α₀ ≤ 0.005`, `ρ : ℝ₊ → ℝ₊` non-decreasing with `ρ(x) + x/(2ρ(x)) ≤ 0.88` for every
`x ∈ (0, α₀]`, `δ ≥ 0.9`, `λ ≥ 0`. Let `Y` be a pure `r`-partite complex of rank `r ≥ 3` that is a
`λ`-product, with local codes `C_uv` on the edges, link codes `C_v = Tan(Y_v, {C_uv})` and global
code `C = Tan(Y, {C_uv})`. If every `C_uv` has distance at least `δ` and every `C_v` is
`(α₀, ρ)`-agreement testable w.r.t. the vertex agreement test on `Y_v`, then `C` is
`(α₀ - √λ, ρ)`-agreement testable w.r.t. the vertex agreement test on `Y`. -/
theorem proposition_5_11_trickle_down {r : ℕ} {V T A : Type*} [Fintype T]
    (Y : PartiteComplex r V T) (Ce : (e : Finset V) → Set (Y.star e → A))
    (α₀ δ lam : ℝ) (ρ : ℝ → ℝ) (hα₀ : α₀ ≤ 0.005)
    (hρ_mono : MonotoneOn ρ (Set.Ici 0)) (hρ_nonneg : ∀ x, 0 ≤ x → 0 ≤ ρ x)
    (hρ : ∀ x ∈ Set.Ioc 0 α₀, 0 < ρ x ∧ ρ x + x / (2 * ρ x) ≤ 0.88)
    (hδ : 0.9 ≤ δ) (hlam : 0 ≤ lam) (hr : 3 ≤ r) (hY : Y.IsLambdaProduct lam)
    (hdist : ∀ e, Y.IsFace e → e.card = 2 →
      Y.HasDistAtLeast (Y.star e) (PartiteComplex.liftCode (Y.star e) (Ce e)) δ)
    (hlink : ∀ (t : T) (i : Fin r), Y.IsVATestable {Y.vert t i} (Y.edgeCodeAt Ce (Y.vert t i))
      (Y.edgeLinkCode Ce (Y.vert t i)) α₀ ρ) :
    Y.IsVATestable ∅ (Y.edgeLinkCode Ce) (Y.edgeTanner Ce) (α₀ - Real.sqrt lam) ρ := by sorry

end LowAccLTC
