-- Prove2me | Theorems.Thm_GeomRescale_lemma_3_8
-- name    : GeomRescale.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:59.597798+00:00
-- url     : https://prove2.me/theorems/b2d16b26-9cae-457b-8b2b-f1ee66a2e480
-- title:
--   Lemma 3.8: $\omega_\mu \ge 1/(4nL_{f,2})$
-- statement:
--   Let $f$ be an integer valued submodular function with $f(\emptyset) = 0$, and let $\mu \in \mathbb{Z}$ satisfy $\min_{S \subseteq V} f(S) < -\mu \le \min\{0, f(V)\}$. Then $\operatorname{width}_{F_\mu}(x) \ge 1/\sqrt{n}$ for every $x \in B(f_\mu)$, and
--
--   $$\omega_\mu \ge \frac{1}{4nL_{f,2}}.$$
--
--   This is the place where integrality of $f$ enters the analysis.
--
--   Differences from the source:
--   - generalization: the conclusion $\omega_\mu \ge 1/(4nL_{f,2})$ → also the bound (12) of the proof; reason: an added conjunct; dropping it gives the printed lemma
--   - encoding: $\min_{S \subseteq V} f(S) < -\mu$ → $\exists S,\ f(S) < -\mu$; reason: same condition on a finite family
--   - encoding: $\omega_\mu$, width as min and max → `sInf` and `sSup`; reason: under these hypotheses $B(f_\mu) \setminus \{0\} = B(f_\mu)$ is compact, so they are attained
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.8, p.11, and display (12)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_fR
import Definitions.Def_GeomRescale_enlarge
import Definitions.Def_GeomRescale_Ltwo
import Definitions.Def_GeomRescale_Fmu
import Definitions.Def_GeomRescale_width
import Definitions.Def_GeomRescale_omega

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace GeomRescale

/-- Lemma 3.8 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.8, p.11, with display (12)): if `f` is an integer valued submodular
function and `μ ∈ ℤ` satisfies `min_{S ⊆ V} f(S) < −μ ≤ min {0, f(V)}`, then
`width_{F_μ}(x) ≥ 1/√n` for every `x ∈ B(f_μ)`, and `ω_μ ≥ 1/(4nL_{f,2})`.

**Formalization Note.** `min_S f(S) < −μ` is written `∃ S, f S < −μ`. The bound (12) is a step of the
proof, kept as a conjunct. -/
theorem lemma_3_8 {n : ℕ} (f : Finset (Fin n) → ℤ) (hsub : Submodular (fR f)) (hf0 : f ∅ = 0)
    (μ : ℤ) (hmin : ∃ S, f S < -μ) (hμ : -μ ≤ min 0 (f Finset.univ)) :
    (∀ x ∈ baseB (enlarge (fR f) (μ : ℝ)), 1 / √(n : ℝ) ≤ width (Fmu (fR f) (μ : ℝ)) x) ∧
      1 / (4 * (n : ℝ) * Ltwo (fR f)) ≤ omega (fR f) (μ : ℝ) := by sorry

end GeomRescale
