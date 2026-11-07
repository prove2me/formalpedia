-- Prove2me | Theorems.Thm_LowAccLTC_lemma_5_4_color_restriction
-- name    : LowAccLTC.lemma_5_4_color_restriction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:40:41.458038+00:00
-- url     : https://prove2.me/theorems/5f87ae1e-36d3-4df1-a122-56d20b89d012
-- title:
--   Lemma 5.4 (Colour-restriction lemma) — agreement testability on most $Y^{\mathcal P}$ gives $(\min(\alpha_0-r^{-1/4},\delta^2/120),\ 220x+4000\rho(x))$-agreement testability
-- statement:
--   Let $\alpha_0\in(0,0.45)$, $\gamma\in(0,10^{-4})$, and ranks $9\le j<0.01\sqrt r$ with $j\mid r$ (the standing assumption of §5). Let $\rho:\mathbb R_+\to\mathbb R_+$ be non-decreasing and concave, and $\delta>\frac{2\rho(\alpha_0)}{1-j/r}+0.1$. Let $X$ be a weighted $r$-partite complex and $\mathrm{Tan}(X,C_0)$ an HDX code such that the code itself and its local codes $C_s$, $s\in X\langle j\rangle\cup X\langle2j\rangle$, all have relative distance at least $\delta$. If for at least a $(1-\gamma)$-fraction of the even partitions $\mathcal P:[r]\to[r/j]$ the code is $(\alpha_0,\rho)$-agreement testable in the colour-restricted complex $Y^{\mathcal P}$ (vertex agreement test of $Y^{\mathcal P}$), then $\mathrm{Tan}(X,C_0)$ is $(\alpha_0',\rho')$-agreement testable over $X$ w.r.t. the $j$-test, where
--   $$\alpha_0'=\min\Big(\alpha_0-r^{-1/4},\ \frac{\delta^2}{120}\Big),\qquad \rho'(x)=220x+4000\rho(x).$$
--
--   It is used for KMS codes with the good partitions of Claim 5.9.
--
--   Differences from the source:
--   - reading: 'for at least a (1 − γ)-fraction of the partition functions P : [r] → [r/j]' → for at least a (1 − γ)-fraction of the even partitions (uniform over even partitions); reason: Y^P is defined only for even partitions (Definition 5.3), and Lemma 6.2's proof samples a random even partition
--   - encoding: Tan(Y^P, C₀) agreement testable in Y^P → IsVATestable on colorRestrict X P with b = ∅, local codes C_s of X for the block j-faces s and target code Tan(X, C₀); reason: Observation 6.1: Tan(Y^P, C₀) = Tan(X, C₀), and the local code of a vertex s of Y^P is C_s
--   - encoding: ρ : ℝ₊ → ℝ₊ non-decreasing and concave → ρ : ℝ → ℝ, ρ ≥ 0, MonotoneOn and ConcaveOn on [0, ∞); reason: only values on [0, ∞) are read
--   - encoding: a pure r-partite simplicial complex with a positive probability measure on its top faces → PartiteComplex: a finite type of top faces with a vertex map vert t i of colour i (colours Fin r, the paper's colour i is i − 1), injective on top faces, and a positive measure μ summing to 1; reason: faces are the subsets of top faces, so this is exactly a pure weighted r-partite complex
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Lemma 5.4, pp.44–45 (PDF pp.47–48); restated as Lemma 6.2, p.54 (PDF p.57); §5 standing j ∣ r, p.42

import Definitions.Def_LowAccLTC_colorRestrict
import Definitions.Def_LowAccLTC_IsVATestable

namespace LowAccLTC

/-- **Lemma 5.4** (The color-restriction lemma; Ben Yaacov–Dikstein–Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs* (manuscript, sha256 04242e17…), pp.44–45 = PDF pp.47–48; restated as
Lemma 6.2, p.54).

Let `α₀ ∈ (0, 0.45)`, `γ ∈ (0, 10^{-4})`, `9 ≤ j < 0.01√r` with `j ∣ r`, `ρ : ℝ₊ → ℝ₊`
non-decreasing and concave, and `δ > 2ρ(α₀)/(1 - j/r) + 0.1`. Let `X` be an `r`-partite complex
and `Tan(X, C₀)` an HDX code such that the code and its local codes `C_s`, `s ∈ X⟨j⟩ ∪ X⟨2j⟩`,
have relative distance at least `δ`. If for at least a `(1 - γ)`-fraction of the even partitions
`P : [r] → [r/j]` the code is `(α₀, ρ)`-agreement testable in `Y^P`, then `Tan(X, C₀)` is
`(α₀', ρ')`-agreement testable over `X` (`j`-test), `α₀' = min(α₀ - r^{-1/4}, δ²/120)`,
`ρ'(x) = 220x + 4000ρ(x)`. -/
theorem lemma_5_4_color_restriction {r : ℕ} {V T A : Type*} [Fintype T]
    (X : PartiteComplex r V T) (C₀ : (u : Finset V) → Set (X.star u → A))
    (α₀ γ δ : ℝ) (ρ : ℝ → ℝ) (j : ℕ)
    (hα₀ : 0 < α₀ ∧ α₀ < 0.45) (hγ : 0 < γ ∧ γ < 1 / 10000) (hj : 9 ≤ j)
    (hjr : (j : ℝ) < 0.01 * Real.sqrt r) (hdvd : j ∣ r)
    (hρ_mono : MonotoneOn ρ (Set.Ici 0)) (hρ_conc : ConcaveOn ℝ (Set.Ici 0) ρ)
    (hρ_nonneg : ∀ x, 0 ≤ x → 0 ≤ ρ x)
    (hδ : 2 * ρ α₀ / (1 - (j : ℝ) / r) + 0.1 < δ)
    (hdist_global : X.HasDistAtLeast Finset.univ (X.tanner C₀) δ)
    (hdist_local : ∀ s, X.IsFace s → (s.card = j ∨ s.card = 2 * j) →
      X.HasDistAtLeast (X.star s) (X.localCode C₀ s) δ)
    (hP : (1 - γ) * ((evenPartitions r j (r / j)).card : ℝ) ≤
      ({P | P ∈ evenPartitions r j (r / j) ∧
        (X.colorRestrict P).IsVATestable ∅ (fun w => X.localCode C₀ w.2) (X.tanner C₀) α₀ ρ}.ncard : ℝ)) :
    X.IsJAgreementTestable C₀ j (min (α₀ - (r : ℝ) ^ (-(1 / 4 : ℝ))) (δ ^ 2 / 120))
      (fun x => 220 * x + 4000 * ρ x) := by sorry

end LowAccLTC
