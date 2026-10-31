-- Prove2me | Theorems.Thm_MaskedLinx_theorem_3_6_limits
-- name    : MaskedLinx.theorem_3_6_limits
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:10.061305+00:00
-- url     : https://prove2.me/theorems/b1f4c051-85fa-43f9-a026-58959d811205
-- title:
--   Theorem 3.6 — $\mathrm{linx}(C,s;\gamma)\to+\infty$ as $\gamma\to0$, and as $\gamma\to+\infty$ when $s<\mathrm{rank}(C)$
-- statement:
--   Let $C$ be a positive semidefinite real matrix of order $n$ and let $0<s<n$. Then
--
--   $$\lim_{\gamma\to0}\mathrm{linx}(C,s;\gamma)=+\infty.$$
--
--   If moreover $s<\mathrm{rank}(C)$, then also
--
--   $$\lim_{\gamma\to+\infty}\mathrm{linx}(C,s;\gamma)=+\infty.$$
--
--   Together with continuity in $\gamma$, the two limits show that the scaled linx bound has a finite minimizing scaling parameter when $s<\mathrm{rank}(C)$ (Corollary 3.7).
--
--   **Formalization Note** `linx` is extended-real valued and $+\infty$ is `⊤`; the limit $\gamma\to0$ is taken through $\gamma>0$ (`𝓝[>] 0`). $\mathrm{rank}(C)$ is `Matrix.rank C` over $\mathbb R$; indices are `Fin n`.
--
--   Differences from the source:
--   - encoding: lim_{γ→0} linx(C,s;γ) = +∞ → Tendsto (fun γ => linx C s γ) (𝓝[>] 0) (𝓝 ⊤) in EReal; reason: the scaling parameter ranges over γ > 0, and +∞ is ⊤ in EReal
-- source:
--   Chen, Fampa, Lee, Masking Anstreicher's linx bound for improved entropy bounds, arXiv:2106.02980v1, Theorem 3.6, p.9

import Mathlib
import Definitions.Def_MaskedLinx_linx

open Filter Topology

namespace MaskedLinx

/-- **Theorem 3.6 (limits of the scaled linx bound as `γ → 0` and `γ → +∞`).**
Chen, Fampa, Lee, *Masking Anstreicher's linx bound for improved entropy bounds*,
arXiv:2106.02980v1, Theorem 3.6, p.9:
"For all positive-semidefinite C and 0 < s < n, we have lim_{γ→0} linx(C,s;γ) = +∞.
If we further assume that s < rank(C), then lim_{γ→+∞} linx(C,s;γ) = +∞."

**Formalization Note.** `linx` is `EReal`-valued and `+∞` is `⊤`; `γ → 0` is the one-sided
limit through `γ > 0` (`𝓝[>] 0`), the domain of the scaling parameter. `rank(C)` is
`Matrix.rank C` over `ℝ`. Indices are `Fin n`. -/
theorem theorem_3_6_limits (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosSemidef)
    (s : ℕ) (hs0 : 0 < s) (hsn : s < n) :
    Tendsto (fun γ : ℝ => linx C s γ) (𝓝[>] 0) (𝓝 ⊤) ∧
    (s < C.rank → Tendsto (fun γ : ℝ => linx C s γ) atTop (𝓝 ⊤)) := by sorry

end MaskedLinx
