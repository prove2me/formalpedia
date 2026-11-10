-- Prove2me | Theorems.Thm_HiddenHardCoreColoring_Mixing_lemma_11
-- name    : HiddenHardCoreColoring.Mixing.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T09:00:04.808659+00:00
-- url     : https://prove2.me/theorems/cc047662-148e-4236-a69a-dfd5d35d329c
-- title:
--   Lemma 11 — adjacent cross terms: lower and upper bounds
-- statement:
--   Throughout, $G=(V,E)$ is a finite simple graph on $n=|V|\ge1$ vertices with $\deg(v)\le\Delta$ for every $v$, $[q]=\{0,\dots,q-1\}$ is the palette, $\Omega$ is the set of proper $q$-colorings, $\mu$ is uniform on $\Omega$, and $q\ge\Delta+3$ (the standing assumption of §§3.2–7). For every edge $uv$ and every $f\in L^2(\mu)$,
--   $$\sum_{c\in[q]}\langle Q_{u,c}f,Q_{v,c}f\rangle_\mu\ge-\frac1{q-\Delta}\Big(\|Q_uf\|_\mu^2+\|Q_vf\|_\mu^2\Big),$$
--   $$\sum_{c\in[q]}\langle Q_{u,c}f,Q_{v,c}f\rangle_\mu\le\langle Q_uf,Q_vf\rangle_\mu+\frac4{9(q-\Delta)^2}\Big(\|Q_uf\|_\mu^2+\|Q_vf\|_\mu^2\Big).$$
--
--   **Formalization Note** Functions on $\Omega$ are all real functions on the subtype of proper colorings; operators are matrices on $\Omega$ acting by $(Mf)(\sigma)=\sum_\tau M(\sigma,\tau)f(\tau)$, and $\langle f,g\rangle_\mu$ is the uniformly weighted sum.
--
--   Differences from the source: none.
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; Lemma 11, p.11

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_Coloring

open Finset Matrix

namespace HiddenHardCoreColoring.Mixing

/-- **Lemma 11** (Xiongxin Yang, STOC 2027 submission #964 (October 2026), p.11). For every edge `uv` and every `f`,
`∑_c ⟨Q_{u,c} f, Q_{v,c} f⟩_µ ≥ −(q − Δ)⁻¹(‖Q_u f‖²_µ + ‖Q_v f‖²_µ)` and
`∑_c ⟨Q_{u,c} f, Q_{v,c} f⟩_µ ≤ ⟨Q_u f, Q_v f⟩_µ + 4/(9(q − Δ)²)(‖Q_u f‖²_µ + ‖Q_v f‖²_µ)`. -/
theorem lemma_11 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ q : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (hq : Δ + 3 ≤ q) (u v : V) (hadj : G.Adj u v) (f : Col G q → ℝ) :
    -(1 / ((q : ℝ) - (Δ : ℝ))) * (sqNorm G q (Qv G q u *ᵥ f) + sqNorm G q (Qv G q v *ᵥ f)) ≤
        ∑ c : Fin q, ip G q (Qvc G q u c *ᵥ f) (Qvc G q v c *ᵥ f) ∧
      ∑ c : Fin q, ip G q (Qvc G q u c *ᵥ f) (Qvc G q v c *ᵥ f) ≤
        ip G q (Qv G q u *ᵥ f) (Qv G q v *ᵥ f) +
          4 / (9 * ((q : ℝ) - (Δ : ℝ)) ^ 2) * (sqNorm G q (Qv G q u *ᵥ f) + sqNorm G q (Qv G q v *ᵥ f)) := by sorry

end HiddenHardCoreColoring.Mixing
