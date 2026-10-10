-- Prove2me | Theorems.Thm_NondomArb_Superhedge_theorem_5_1_c
-- name    : NondomArb.Superhedge.theorem_5_1_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:24:06.316132+00:00
-- url     : https://prove2.me/theorems/6b01a6df-ccaa-468c-a9cd-7c38c3d7a1cb
-- title:
--   Theorem 5.1(c) — second fundamental theorem: f replicable ⟺ Q ↦ E_Q[f] constant on 𝒬_φ ⟺ every P dominated by Q with E_Q[f] = π(f)
-- statement:
--   Consider the multi-period market of §1.2 with $d$ stocks and $e$ options, and $\mathcal Q_\varphi=\{Q\in\mathcal Q: E_Q[\varphi]<\infty\}$. A random variable $f$ is *replicable* if $x+H\bullet S_T+hg=f$ $\mathcal P$-q.s. for some $x\in\mathbb R$ and $(H,h)\in\mathcal H\times\mathbb R^e$.
--
--   **Theorem.** Let $\varphi\ge1$ be a random variable with $|g^i|\le\varphi$ for $i=1,\dots,e$. Let NA($\mathcal P$) hold, and let $f:\Omega\to\mathbb R$ be upper semianalytic with $|f|\le\varphi$. The following are equivalent:
--   1. $f$ is replicable;
--   2. the mapping $Q\mapsto E_Q[f]\in\mathbb R$ is constant on $\mathcal Q_\varphi$;
--   3. for all $P\in\mathcal P$ there exists $Q\in\mathcal Q_\varphi$ such that $P\ll Q$ and $E_Q[f]=\pi(f)$.
--
--   This is the paper's Second Fundamental Theorem in its weighted form.
--
--   **Formalization Note** Condition 2 reads: there is a real number $c$ with $E_Q[f]=c$ for every $Q\in\mathcal Q_\varphi$. Expectations are the extended expectations (1.1) and $\pi(f)$ is the `EReal` superhedging price.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 30, Theorem 5.1(c); p. 7 (replicable)

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_Model
open MeasureTheory BertsekasShreve.AnalyticSelection

namespace NondomArb.Superhedge

/-- **Theorem 5.1(c)** (p. 30). Second fundamental theorem with options: for a random variable
`φ ≥ 1` with `|gⁱ| ≤ φ`, under NA(𝒫) and for `f` upper semianalytic with `|f| ≤ φ`, the following
are equivalent: (i) `f` is replicable; (ii) `Q ↦ E_Q[f] ∈ ℝ` is constant on `𝒬_φ`; (iii) every
`P ∈ 𝒫` is absolutely continuous with respect to some `Q ∈ 𝒬_φ` with `E_Q[f] = π(f)`. -/
theorem theorem_5_1_c {Ω₁ : Type*} [TopologicalSpace Ω₁] [PolishSpace Ω₁]
    [MeasurableSpace Ω₁] [BorelSpace Ω₁] {T d : ℕ} {e : ℕ}
    (M : Market Ω₁ T d e) (hM : M.Standing)
    (φ : (Fin T → Ω₁) → ℝ) (hφ : IsUMeasurable φ) (hφ1 : ∀ ω, 1 ≤ φ ω)
    (hgφ : ∀ ω (i : Fin e), |M.g ω i| ≤ φ ω)
    (hNA : M.NA) (f : (Fin T → Ω₁) → ℝ) (hf : IsUpperSemianalytic (fun ω => (f ω : EReal)))
    (hfφ : ∀ ω, |f ω| ≤ φ ω) :
    List.TFAE [M.Replicable f,
      ∃ c : ℝ, ∀ Q ∈ M.MartMeasuresWeighted φ, extExp Q (fun ω => (f ω : EReal)) = (c : EReal),
      ∀ P ∈ M.models, ∃ Q ∈ M.MartMeasuresWeighted φ, P ≪ Q ∧
        extExp Q (fun ω => (f ω : EReal)) = M.price f] := by sorry

end NondomArb.Superhedge
