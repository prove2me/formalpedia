-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_lemma_42
-- name    : GaussLocalMaxColoring.Main.lemma_42
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:23:35.307519+00:00
-- url     : https://prove2.me/theorems/83927c99-be05-4c1c-a139-82406c39ba73
-- title:
--   Lemma 42 — Gaussian bounds for the global (i) and local (ii) induction steps
-- statement:
--   Section 5 setting under the analysis convention (exact edge constraint), any nested core sequence $V=F_0\supseteq F_1\supseteq\cdots$, any vertex $r$ (with $\rho_x,u_x$ for this root), and $n$ (hence $t$) sufficiently large. Let $1\le j\le\ell$ and $1.968\le A\le A'\le A_0$ with $A'-A\le w$, and assume $p_{F_{j-1}}(x)\le e^{-t^2/2}$ and $\mathbb P_g[M_{F_{j-1}}(x)>A't]\le t^{-4}\overline\Phi(t/2)$ for every $x\in F_j$. Then:
--   (i) for $x\in F_j$ with $\|u_x\|>0$ and $q_A(\rho_x)<q_c(\rho_x)$, any parameters $(a,b,\mu,c,\kappa,\theta)$ of Case 1 of Lemma 40 (with $A$ and $\rho=\rho_x$) and $L=q_A(\rho_x)/\sqrt{1-\rho_x^2}$,
--   $$\mathbb P_g\big[|\langle g,u_x\rangle|>L\|u_x\|t,\ |\langle g,u_y\rangle|\le q_{A'}(\rho_y)t\ \forall y\in N_{F_{j-1}}(x)\big]\le2\overline\Phi(Lt)\,\overline\Phi((\mu+\theta(\mu+\kappa))t);$$
--   (ii) if $\Gamma_{rx}(X)\succeq0$ for every $x\in N_{F_j}(r)$ ($X$ the Gram matrix of $\{v_x\}$), then for any parameters of Case 2 of Lemma 40 (with $A$), with $\mathcal L=\{M_{F_j}(r)>At\}$ and $x$ the maximizer of $M_{F_j}(r)$, for all $p_1,p_2>1$ with $(p_1-1)(p_2-1)\ge\tfrac14$,
--   $$\mathbb P_g\big[\mathcal L,\ -\langle g,u_y\rangle\le q_{A'}(\rho_y)t\ \forall y\in N_{F_{j-1}}(x)\big]\le\big(|N_{F_j}(r)|\overline\Phi(At)\big)^{1-1/p_1}\,\overline\Phi((\mu+\theta(\mu+\kappa))t)^{1/p_2}\,\mathbb P_g[\mathcal L]^{1/p_1}.$$
--
--   Differences from the source:
--   - generalization: the cores F₀ ⊇ ⋯ ⊇ F_ℓ produced by Algorithm 2 → any ℕ-indexed nested sequence F with F 0 = V; reason: the lemma's proof uses only the stated hypotheses on the cores; Algorithm 2's cores extended by F_j = F_ℓ for j > ℓ are an instance
--   - generalization: "take the parameters (a, b, μ, c, κ, θ) from the corresponding case of Lemma 40" → every parameter tuple satisfying the conditions of that case (L40Case1 with A and ρ_x, L40Case2 with A); reason: Lemma 40 only asserts existence; the proof uses only conditions (i)–(iv)
--   - reading: "for sufficiently large t" (t = √((1−β) log n), Table 3) → ∃ N₀, ∀ n ≥ N₀, with N₀ chosen before every graph, vector family, core sequence and parameter; reason: the asymptotic convention of the paper (uniform thresholds); t is increasing in n
--   - encoding: §5 analysis convention: the edge constraint of Lemma 34 is treated as exact (p. 35) → ExactSDPVectors G v: unit vectors, −1/2 ≤ ⟨v_i, v_j⟩ ≤ 1, ⟨v_i, v_j⟩ = −1/2 on edges, the third constraint of Lemma 34; reason: the analysis of §5.4–5.5 is stated under this convention (justified in Appendix B.2)
--   - encoding: "on ℒ, let x denote the maximizer of M_{F_j}(r)" (ties broken by the fixed total order) → nbrArgmax: the least maximizer in the order of Fin n; reason: the paper does not say which end of the order wins a tie
--   - encoding: §5 standing assumptions (G 3-colorable, every degree ≤ n^β, β = 0.692601; Table 3 parameters as functions of n) → binders G.Colorable 3, maxDegOn G univ ≤ n^beta5, and the Table 3 definitions of the Section5 module; reason: the section states them once (pp. 31, 35); they are hypotheses of every §5 lemma
--   - encoding: vertex set V with a fixed total order breaking ties → V = Fin n with its order; reason: Lean convention; every finite ordered vertex set is relabelled this way
--   - encoding: vectors in R^d, g ∼ N(0, I_d), P_g → Space d = EuclideanSpace ℝ (Fin d), any d, Mathlib stdGaussian (gaussProb); reason: Lean convention; same instances
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Lemma 42, printed p. 43 (PDF 45)

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Bands

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical

namespace GaussLocalMaxColoring.Main

/-- **Lemma 42** (p. 43, PDF 45). Section 5 setting (analysis convention: exact edge constraint),
any nested core sequence `V = F₀ ⊇ F₁ ⊇ ⋯`, any vertex `r`, and `n` (hence `t`) sufficiently
large. Let `1 ≤ j ≤ ℓ`, `1.968 ≤ A ≤ A′ ≤ A₀`, `A′ − A ≤ w`, and assume `p_{F_{j−1}}(x) ≤ e^{−t²/2}`
and `P_g[M_{F_{j−1}}(x) > A′t] ≤ t^{−4} Φ̄(t/2)` for every `x ∈ F_j`. Then:
(i) for `x ∈ F_j` with `‖u_x‖ > 0`, `q_A(ρ_x) < q_c(ρ_x)`, any parameters of Case 1 of Lemma 40
(with `A`, `ρ = ρ_x`) and `L = q_A(ρ_x)/√(1−ρ_x²)`,
`P_g[|⟨g, u_x⟩| > L‖u_x‖t, |⟨g, u_y⟩| ≤ q_{A′}(ρ_y)t ∀ y ∈ N_{F_{j−1}}(x)] ≤ 2Φ̄(Lt)Φ̄((μ+θ(μ+κ))t)`;
(ii) if `Γ_rx(X) ⪰ 0` for every `x ∈ N_{F_j}(r)` (`X` the Gram matrix), then for any parameters of
Case 2 of Lemma 40 (with `A`), with `ℒ = {M_{F_j}(r) > At}` and `x` the maximizer of `M_{F_j}(r)`,
for all `p₁, p₂ > 1` with `(p₁−1)(p₂−1) ≥ 1/4`,
`P_g[ℒ, −⟨g, u_y⟩ ≤ q_{A′}(ρ_y)t ∀ y ∈ N_{F_{j−1}}(x)]
  ≤ (|N_{F_j}(r)| Φ̄(At))^{1−1/p₁} Φ̄((μ+θ(μ+κ))t)^{1/p₂} P_g[ℒ]^{1/p₁}`. -/
theorem lemma_42 :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ (d : ℕ) (G : SimpleGraph (Fin n)), G.Colorable 3 →
      (maxDegOn G Finset.univ : ℝ) ≤ (n : ℝ) ^ beta5 →
      ∀ v : Fin n → Space d, ExactSDPVectors G v →
      ∀ F : ℕ → Finset (Fin n), F 0 = Finset.univ → (∀ i, F (i + 1) ⊆ F i) →
      ∀ (r : Fin n) (j : ℕ), 1 ≤ j → j ≤ numLevels n →
      ∀ A A' : ℝ, 1968 / 1000 ≤ A → A ≤ A' → A' ≤ A0 → A' - A ≤ w5 n →
      (∀ x ∈ F j, pLocal G v (F (j - 1)) x ≤ Real.exp (-(t5 n ^ 2 / 2)) ∧
        gaussProb {g : Space d | ((A' * t5 n : ℝ) : WithBot ℝ) < nbrMax G v (F (j - 1)) x g} ≤
          (t5 n ^ 4)⁻¹ * PhiTail (t5 n / 2)) →
      (∀ x ∈ F j, 0 < ‖uvec v r x‖ → qA A (rho v r x) < qc (rho v r x) →
        ∀ a b μ c κ θ : ℝ, L40Case1 A (rho v r x) a b μ c κ θ →
          gaussProb {g : Space d |
              qA A (rho v r x) / Real.sqrt (1 - rho v r x ^ 2) * ‖uvec v r x‖ * t5 n <
                |⟪g, uvec v r x⟫| ∧
              ∀ y ∈ nbr G (F (j - 1)) x, |⟪g, uvec v r y⟫| ≤ qA A' (rho v r y) * t5 n} ≤
            2 * PhiTail (qA A (rho v r x) / Real.sqrt (1 - rho v r x ^ 2) * t5 n) *
              PhiTail ((μ + θ * (μ + κ)) * t5 n)) ∧
      ((∀ x ∈ nbr G (F j) r, (Gamma G (gram v) r x).PosSemidef) →
        ∀ a b μ c κ θ : ℝ, L40Case2 A a b μ c κ θ →
        ∀ p₁ p₂ : ℝ, 1 < p₁ → 1 < p₂ → 1 / 4 ≤ (p₁ - 1) * (p₂ - 1) →
          gaussProb {g : Space d | ((A * t5 n : ℝ) : WithBot ℝ) < nbrMax G v (F j) r g ∧
              ∀ y ∈ nbr G (F (j - 1)) (nbrArgmax G v (F j) r g),
                -⟪g, uvec v r y⟫ ≤ qA A' (rho v r y) * t5 n} ≤
            ((nbr G (F j) r).card * PhiTail (A * t5 n)) ^ (1 - 1 / p₁) *
              PhiTail ((μ + θ * (μ + κ)) * t5 n) ^ (1 / p₂) *
              gaussProb {g : Space d | ((A * t5 n : ℝ) : WithBot ℝ) < nbrMax G v (F j) r g} ^
                (1 / p₁)) := by sorry

end GaussLocalMaxColoring.Main
