-- Prove2me | Theorems.Thm_OnlineCRS_Submod_lemma_3_5
-- name    : OnlineCRS.Submod.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:35.239415+00:00
-- url     : https://prove2.me/theorems/c113ff80-33c1-4e68-a0dd-ad60559b1f55
-- title:
--   Lemma 3.5, p. 17 — a pruning η_f makes every monotone (b, c)-balanced CRS c-competitive for F(x)
-- statement:
--   Let $f:2^N\to\mathbb R_{\ge0}$ be a non-negative submodular function with multilinear extension $F(x)=\mathbb E[f(R(x))]$. There exists a map $\eta_f:2^N\to 2^N$, depending on $f$ only, with $\eta_f(S)\subseteq S$ for every $S\subseteq N$, such that the following holds. For every $b,c\in[0,1]$, every $P\subseteq[0,1]^N$, every monotone $(b,c)$-balanced CRS $\pi$ for $P$ and every input $x\in bP$,
--   $$\mathbb E\big[f(\eta_f(\pi(R(x))))\big]\ge c\cdot F(x).$$
--
--   The lemma follows from the work of Chekuri, Vondrák and Zenklusen (mostly their Theorem 1.3) and is not proved in this paper. It is the step that converts the balancedness of the characteristic CRS into an approximation guarantee for submodular objectives.
--
--   **Formalization Note** The order of quantifiers is the paper's: $\eta_f$ is chosen before $P$, $b$, $c$, $\pi$ and $x$. Balancedness is the corrected Definition 3.1 ("$\ge c$"). The polytope $P$ is an arbitrary subset of $[0,1]^N$; no polyhedrality is assumed.
-- source:
--   arXiv:1508.00142v2, Lemma 3.5, p. 17 (from Chekuri, Vondrák, Zenklusen, SIAM J. Comput. 43(6), 2014, Theorem 1.3)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_OnlineCRS_Matroid_Basics
import Definitions.Def_OnlineCRS_Submod_Model
import Definitions.Def_OnlineCRS_Submod_CRS

open scoped Pointwise

namespace OnlineCRS.Submod

/-- Lemma 3.5 (arXiv:1508.00142v2, p. 17; from Chekuri–Vondrák–Zenklusen, Theorem 1.3): for every
non-negative submodular `f` there is a map `η_f` with `η_f(S) ⊆ S`, depending on `f` only, such that for
every monotone `(b, c)`-balanced CRS `π` for a polytope `P ⊆ [0,1]^N` and every `x ∈ bP`,
`E[f(η_f(π(R(x))))] ≥ c · F(x)`. -/
theorem lemma_3_5 {α : Type} [Fintype α] [DecidableEq α] (f : Finset α → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) :
    ∃ η : Finset α → Finset α, (∀ S, η S ⊆ S) ∧
      ∀ (P : Set (α → ℝ)), IsPolytope P → ∀ (b c : ℝ),
        0 ≤ b → b ≤ 1 → 0 ≤ c → c ≤ 1 →
        (∀ y ∈ P, ∀ e : α, 0 ≤ y e ∧ y e ≤ 1) →
        ∀ ρ : (α → ℝ) → (Finset α → Finset α) → ℝ,
          IsCRS P ρ → IsBalanced P b c ρ → IsMonotoneCRS ρ →
          ∀ x ∈ b • P,
            c * NonmonotoneSubmod.Shared.F f x ≤
              ∑ A : Finset α, OnlineCRS.Matroid.activeProb x A *
                ∑ φ : Finset α → Finset α, ρ x φ * f (η (φ A)) := by sorry

end OnlineCRS.Submod
