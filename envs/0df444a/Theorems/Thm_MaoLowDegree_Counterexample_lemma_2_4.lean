-- Prove2me | Theorems.Thm_MaoLowDegree_Counterexample_lemma_2_4
-- name    : MaoLowDegree.Counterexample.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:44.08048+00:00
-- url     : https://prove2.me/theorems/e1264362-e5bd-4ae4-bff8-3ecccbfae00d
-- title:
--   Lemma 2.4 — independent evaluation vectors
-- statement:
--   Fix the numerical parameters of p.8. For all sufficiently large $n$, let $W\le\mathrm{RM}(m,r)$ have a basis $f_1,\ldots,f_K$ and satisfy $|\operatorname{bias}(f)|\le\eta$ for every nonzero $f\in W$. There are points $x_1,\ldots,x_n\in\mathbb F_2^m$ whose evaluation vectors $v_i=(f_1(x_i),\ldots,f_K(x_i))$ satisfy
--   $$\{v_i:i\in I\}\text{ is linearly independent for every }I\subseteq[n],\ |I|\le L,$$
--   where $L=\lfloor K/(4\ell_n)\rfloor$.
--
--   This is the precise independence property used for local graph uniformity. The statement allows every qualifying subspace and basis, with a threshold depending only on the numerical parameters.
--
--   Differences from the source:
--   - encoding: vertices 1 through n and unordered edges → Fin n with increasing endpoint pairs; n=0 is an empty-cube extension; reason: relabeling by subtracting one changes no positive-n instance
--   - encoding: for all sufficiently large n and probability 1-o(1) → Filter.atTop eventual assertions and Tendsto to 1; reason: these are the literal asymptotic quantifiers, with all fixed parameters before n
--   - generalization: a low-bias subspace and its basis fixed above the lemma → a sufficiently-large-n threshold uniform over every qualifying W and basis; reason: the probability bound on p.9 depends only on n,K,eta,L, so this specializes to every fixed choice made by the source
-- source:
--   Songtao Mao, STOC 2027 submission #509 (October 2026), Lemma 2.4, p.9; setup, pp.8–9

import Definitions.Def_MaoLowDegree_Counterexample_computationalClaims

open Classical Filter
open scoped Topology
noncomputable section
set_option autoImplicit false

namespace MaoLowDegree.Counterexample

/-- Lemma 2.4, p.9. The threshold is uniform over the fixed low-bias subspace and its basis. -/
theorem lemma_2_4 (r : ℕ) (β₁ β₂ b κ : ℝ)
    (hparams : Admissible r β₁ β₂ b κ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ W : Submodule F₂ (Vec (ambientDimension b n) → F₂),
      W ≤ RM (ambientDimension b n) r → LowBias W (eta r β₁ b n) →
      ∀ f : Module.Basis (Fin (codeDimension r b κ n)) F₂ W,
        ∃ x : Fin n → Vec (ambientDimension b n),
          WiseIndependent (fun j i => (f i).val (x j)) (independenceLength r b κ n) := by sorry

end MaoLowDegree.Counterexample
