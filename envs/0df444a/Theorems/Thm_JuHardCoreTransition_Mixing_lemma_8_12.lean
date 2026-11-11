-- Prove2me | Theorems.Thm_JuHardCoreTransition_Mixing_lemma_8_12
-- name    : JuHardCoreTransition.Mixing.lemma_8_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:17:42.372302+00:00
-- url     : https://prove2.me/theorems/1a6085e4-f4e5-4a98-968f-3d197eb3296d
-- title:
--   Lemma 8.12 — simplicity probabilities for zero, one and two replicas
-- statement:
--   Fix $d\ge3$, $K>0$ and $j\in\{0,1,2\}$. For $j=1,2$ let $\xi=\alpha$ or $\Gamma$ range over a fixed compact set on which all state proportions and all coupling entries with $B_{aa'}=1$, respectively $B_{aa'}B_{bb'}=1$, are positive; for $j=0$ let $\xi=(1)$. Let $R$ specify $q_N\le K\sqrt N$ disjoint edges of $M_{v,1}$ and their endpoint states, and use the residual law $P^{(j)}_\xi(\cdot\mid R)$. Let $X$ count cycles of length two (a base edge and two colours containing it; exposed edges included). With $\Lambda_0=\frac{d(d-1)}4$, $\Lambda_1(\alpha)=\frac{d(d-1)}4\operatorname{tr}(T_\alpha^2)$, $\Lambda_2(\Gamma)=\frac{d(d-1)}4\operatorname{tr}((T^{(2)}_\Gamma)^2)$ and $a_j(\xi)=e^{-\Lambda_j(\xi)}$, there are $C,N_0>0$, depending only on $d$, $K$ and the compact set, such that for even $N\ge N_0$ and uniformly after every admissible exposure $R$,
--   $$\Big|\log\frac{P^{(j)}_\xi(X=0\mid R)}{a_j(\xi)}\Big|\le\frac C{\sqrt N}.$$
--   Moreover $P^{(j)}_\xi(X=0\mid R)\ge\frac12e^{-4d(d-1)}$. Each $a_j$ is analytic in $\xi$ on a neighbourhood of the compact set. For rational $K$ and a compact type set specified by rational coordinate bounds, $C,N_0$ can be computed from $d$, $K$ and these bounds.
--
--   Differences from the source:
--   - encoding: the residual law P^{(j)}_ξ(· | R) and the event X = 0 → the uniform law on admissible d-tuples of perfect matchings (simpleProb) and IsSimpleTuple; reason: the residual law is a product of uniform laws on the sets of compatible completions, i.e. uniform on their product
--   - encoding: j = 0, 1, 2 with ξ = (1), α, Γ → three conjuncts with state spaces Unit (all compatible), Fin 4 with B, Fin 4 × Fin 4 with B ⊗ B; ξ = the state proportions of the fixed labels; reason: same instances
--   - encoding: ξ ranges over a fixed compact set with positive proportions and positive permitted coupling entries → ∀ Kset with IsAdmissibleTypeSet (compact, inside the probability simplex, positivity as stated), ∃ C, N₀ > 0; reason: C, N₀ depend only on d, K and the compact set
--   - generalization: a_j analytic in ξ on a neighbourhood of the compact set → analytic on an open set of ℝ^S containing the compact set (P(ξ) defined by row sums, so off-simplex ξ are allowed); reason: on a neighborhood of the compact admissible set the entropy maximizer has positive permitted entries and an analytic exponential-tilt parametrization; positive scaling extends it off the simplex, and restriction recovers the source statement
--   - encoding: C, N₀ can be computed from d, K and rational coordinate bounds → ∃ F Computable on naturals with C = qOf, N₀ the outputs; nonnegative rationals encoded by (p, q) ↦ p/(q+1); the type set is the simplex cut out by the bounds (boxTypeSet), assumed admissible; reason: computability over encoded rationals
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), Lemma 8.12, printed p.92 / PDF p.93

import Mathlib
import Definitions.Def_JuHardCoreTransition_Mixing_GadgetRate
import Definitions.Def_JuHardCoreTransition_Mixing_Simplicity

namespace JuHardCoreTransition.Mixing

/-- **Lemma 8.12 (Simplicity probabilities)** (printed p.92 / PDF p.93). Fix `d ≥ 3`, `K > 0` and
`j ∈ {0, 1, 2}`; `ξ = (1)` (one state, everything compatible) for `j = 0`, `ξ = α` (states `Ω`,
compatibility `B`) for `j = 1`, `ξ = Γ` (states `Ω²`, compatibility `B ⊗ B`) for `j = 2`, ranging
for `j = 1, 2` over a fixed compact set on which all state proportions and all permitted entries
of the entropy-maximising coupling are positive. With `Λ₀ = d(d−1)/4`,
`Λ₁(α) = d(d−1) tr(T_α²)/4`, `Λ₂(Γ) = d(d−1) tr((T_Γ^{(2)})²)/4` and `a_j = e^{−Λ_j}`, there are
`C, N₀ > 0` depending only on `d, K` and the compact set such that for even `N ≥ N₀`, uniformly
after every admissible exposure `R` of `q_N ≤ K√N` edges of the first matching,
`|log(P_ξ^{(j)}(X = 0 | R)/a_j(ξ))| ≤ C/√N`, and `P_ξ^{(j)}(X = 0 | R) ≥ ½ e^{−4d(d−1)}`.
Each `a_j` is analytic on a neighbourhood of the compact set. Moreover (last conjunct), for
rational `K` and a compact type set specified by rational coordinate bounds, `C` and `N₀` are
computable from `d`, `K` and these bounds (nonnegative rationals encoded by `qOf`). -/
theorem lemma_8_12 :
    (∀ d : ℕ, 3 ≤ d → ∀ K : ℝ, 0 < K →
      -- j = 0
      (∃ C : ℝ, ∃ N₀ : ℕ, 0 < N₀ ∧
        SimplicityBoundsHold (S := Unit) (fun _ _ => True)
          (fun _ => Real.exp (-((d : ℝ) * ((d : ℝ) - 1) / 4))) d K C N₀ Set.univ) ∧
      -- j = 1
      (∀ Kset : Set (Fin 4 → ℝ), IsAdmissibleTypeSet compat Kset →
        (∃ C : ℝ, ∃ N₀ : ℕ, 0 < N₀ ∧
          SimplicityBoundsHold compat (fun α => Real.exp (-limitMean d compat α)) d K C N₀ Kset) ∧
        ∃ O : Set (Fin 4 → ℝ), IsOpen O ∧ Kset ⊆ O ∧
          AnalyticOnNhd ℝ (fun α => Real.exp (-limitMean d compat α)) O) ∧
      -- j = 2
      (∀ Kset : Set (Fin 4 × Fin 4 → ℝ), IsAdmissibleTypeSet compat2 Kset →
        (∃ C : ℝ, ∃ N₀ : ℕ, 0 < N₀ ∧
          SimplicityBoundsHold compat2 (fun Γ => Real.exp (-limitMean d compat2 Γ)) d K C N₀
            Kset) ∧
        ∃ O : Set (Fin 4 × Fin 4 → ℝ), IsOpen O ∧ Kset ⊆ O ∧
          AnalyticOnNhd ℝ (fun Γ => Real.exp (-limitMean d compat2 Γ)) O)) ∧
    -- effectivity: `C` and `N₀` computable from `d`, rational `K` and rational coordinate bounds
    (∃ F₀ : ℕ × (ℕ × ℕ) → (ℕ × ℕ) × ℕ, Computable F₀ ∧
      ∀ d : ℕ, 3 ≤ d → ∀ k : ℕ × ℕ, 0 < qOf k →
        0 < (F₀ (d, k)).2 ∧
        SimplicityBoundsHold (S := Unit) (fun _ _ => True)
          (fun _ => Real.exp (-((d : ℝ) * ((d : ℝ) - 1) / 4))) d (qOf k) (qOf (F₀ (d, k)).1)
          (F₀ (d, k)).2 Set.univ) ∧
    (∃ F₁ : ℕ × (ℕ × ℕ) × (Fin 4 → (ℕ × ℕ) × (ℕ × ℕ)) → (ℕ × ℕ) × ℕ, Computable F₁ ∧
      ∀ d : ℕ, 3 ≤ d → ∀ (k : ℕ × ℕ) (bd : Fin 4 → (ℕ × ℕ) × (ℕ × ℕ)), 0 < qOf k →
        IsAdmissibleTypeSet compat (boxTypeSet (fun a => qOf (bd a).1) (fun a => qOf (bd a).2)) →
        0 < (F₁ (d, k, bd)).2 ∧
        SimplicityBoundsHold compat (fun α => Real.exp (-limitMean d compat α)) d (qOf k)
          (qOf (F₁ (d, k, bd)).1) (F₁ (d, k, bd)).2
          (boxTypeSet (fun a => qOf (bd a).1) (fun a => qOf (bd a).2))) ∧
    (∃ F₂ : ℕ × (ℕ × ℕ) × (Fin 4 → Fin 4 → (ℕ × ℕ) × (ℕ × ℕ)) → (ℕ × ℕ) × ℕ, Computable F₂ ∧
      ∀ d : ℕ, 3 ≤ d → ∀ (k : ℕ × ℕ) (bd : Fin 4 → Fin 4 → (ℕ × ℕ) × (ℕ × ℕ)), 0 < qOf k →
        IsAdmissibleTypeSet compat2
          (boxTypeSet (fun x => qOf (bd x.1 x.2).1) (fun x => qOf (bd x.1 x.2).2)) →
        0 < (F₂ (d, k, bd)).2 ∧
        SimplicityBoundsHold compat2 (fun Γ => Real.exp (-limitMean d compat2 Γ)) d (qOf k)
          (qOf (F₂ (d, k, bd)).1) (F₂ (d, k, bd)).2
          (boxTypeSet (fun x => qOf (bd x.1 x.2).1) (fun x => qOf (bd x.1 x.2).2))) := by sorry

end JuHardCoreTransition.Mixing
