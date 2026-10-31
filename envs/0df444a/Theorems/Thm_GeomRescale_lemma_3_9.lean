-- Prove2me | Theorems.Thm_GeomRescale_lemma_3_9
-- name    : GeomRescale.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:43.772101+00:00
-- url     : https://prove2.me/theorems/ffa63009-400c-4b55-9aeb-1105d87e4bae
-- title:
--   Lemma 3.9: $\Gamma \subseteq B(f_\mu)$ and the form (13) of $R$
-- statement:
--   At every stage of Algorithm Rescaling-SFM, $\Gamma \subseteq B(f_\mu)$ for the current $\mu$. After $t$ rescalings, the current matrix $R$ is of the form
--
--   $$R = \alpha I_n + \sum_{g \in \Gamma} \gamma_g \frac{g g^{\mathsf T}}{\|g\|_2^2},$$
--
--   where $\alpha = 1/(1 + \varepsilon)^{2t}$ and $\gamma_g > 0$ for all $g \in \Gamma$.
--
--   The analysis of Lemmas 3.10–3.13 rests on this form.
--
--   Differences from the source:
--   - reading: denominator $\|g\|_2$ in (13) as printed → denominator $\|g\|_2^2$; reason: the proof of Lemma 3.13, display (30), and its trace computation use $\|g\|_2^2$; every $g \in \Gamma$ is nonzero and $\gamma_g$ is free, so the two forms are equivalent
--   - encoding: throughout the algorithm / at every stage → every state reachable from the initial state, for $f, \Lambda$ as in the goal; reason: a run is a relation, so this covers all tie-breaks and argmins; the placeholder $\mu, W$ of the state before lines 2–3 is included, and the statement holds there too
--   - encoding: the set $\Gamma$ → the underlying finite set of a list; reason: a vector found twice is one element, with the sum of its coefficients
--   - encoding: a ground set $V$ with $n = |V|$ elements → `1 ≤ n`; reason: the parameter $\varepsilon = 1/(20n)$ of Algorithm 2 is undefined at $n = 0$; the hypothesis excludes only that case
--   - generalization: the run of Algorithm 2 with $T = 5n\log(nL_{f,2})$ → the runs for every $\Lambda \ge L_{f,2}$, with $T = \lceil 5n\log_2(n\Lambda)\rceil_+$; reason: $\Lambda = L_{f,2}$ gives the paper's run, with $T$ rounded as in Theorem 3.6; the statement holds on every such run
--   - reading: $g/\|g\|_Q$ with no case for $g = 0$ → $g/\|g\|_Q := 0$ at $g = 0$ in the step relation; reason: $g = 0$ occurs (for $f \equiv 0$ at line 2 of Algorithm 1), and the run needs a value there
--   - reading: $g_1, \dots, g_k$ in (10) and in line 8 of Algorithm 2, returned after line 15 of Algorithm 1 incremented $k$ → $g_1, \dots, g_{k-1}$, the bases the call computed; reason: line 15 has incremented $k$, so no $g_k$ was computed
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.9 and display (13), p.11

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_fR
import Definitions.Def_GeomRescale_enlarge
import Definitions.Def_GeomRescale_norm2
import Definitions.Def_GeomRescale_eps
import Definitions.Def_GeomRescale_Ltwo
import Definitions.Def_GeomRescale_Reachable

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg
open Classical

namespace GeomRescale

/-- Lemma 3.9 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.9 and display (13), p.11): at every stage of Algorithm Rescaling-SFM,
`Γ ⊆ B(f_μ)`, and after `t` rescalings `R = αI_n + ∑_{g ∈ Γ} γ_g ggᵀ/‖g‖₂²`, with
`α = 1/(1 + ε)^{2t}` and `γ_g > 0` for all `g ∈ Γ`.

**Formalization Note.** "At every stage" is every reachable state; `t` is the counter `s.i` of
completed rescalings. The set `Γ` is `s.Γ.toFinset`, and `μ` is the current `s.vn.μ`. The page prints the
denominator of (13) as `‖g‖₂`, but the proof of Lemma 3.13, display (30), and the trace computation after it
use `‖g‖₂²`, which is stated here; since every `g ∈ Γ` is nonzero and `γ_g` is free, the two forms say the
same thing. -/
theorem lemma_3_9 {n : ℕ} (hn : 1 ≤ n) (f : Finset (Fin n) → ℤ) (hsub : Submodular (fR f))
    (hf0 : f ∅ = 0) (Λ : ℝ) (hΛ : Ltwo (fR f) ≤ Λ) (s : St n) (hs : Reachable f Λ s) :
    (∀ g ∈ s.Γ, g ∈ baseB (enlarge (fR f) (s.vn.μ : ℝ))) ∧
      ∃ γ : (Fin n → ℝ) → ℝ, (∀ g ∈ s.Γ, 0 < γ g) ∧
        s.R = (1 / (1 + eps n) ^ (2 * s.i)) • (1 : Matrix (Fin n) (Fin n) ℝ) +
          ∑ g ∈ s.Γ.toFinset, (γ g / norm2 g ^ 2) • Matrix.vecMulVec g g := by sorry

end GeomRescale
