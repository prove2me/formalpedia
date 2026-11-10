-- Prove2me | Theorems.Thm_HiddenHardCoreColoring_Mixing_lemma_10
-- name    : HiddenHardCoreColoring.Mixing.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:59:57.043103+00:00
-- url     : https://prove2.me/theorems/1988db2d-c12b-44c4-ae3b-f4fea942a367
-- title:
--   Lemma 10 — non-adjacent cross terms: 0 ≤ ∑_c ⟨Q_{u,c}f, Q_{v,c}f⟩ ≤ (1 + 2/(q−Δ))⟨Q_u f, Q_v f⟩
-- statement:
--   Throughout, $G=(V,E)$ is a finite simple graph on $n=|V|\ge1$ vertices with $\deg(v)\le\Delta$ for every $v$, $[q]=\{0,\dots,q-1\}$ is the palette, $\Omega$ is the set of proper $q$-colorings, $\mu$ is uniform on $\Omega$, and $q\ge\Delta+3$ (the standing assumption of §§3.2–7). For distinct non-adjacent vertices $u,v$ and every $f\in L^2(\mu)$,
--   $$0\le\sum_{c\in[q]}\langle Q_{u,c}f,Q_{v,c}f\rangle_\mu\le\Big(1+\frac2{q-\Delta}\Big)\langle Q_uf,Q_vf\rangle_\mu .$$
--
--   **Formalization Note** Functions on $\Omega$ are all real functions on the subtype of proper colorings; operators are matrices on $\Omega$ acting by $(Mf)(\sigma)=\sum_\tau M(\sigma,\tau)f(\tau)$, and $\langle f,g\rangle_\mu$ is the uniformly weighted sum.
--
--   Differences from the source: none.
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; Lemma 10, p.11

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_Coloring

open Finset Matrix

namespace HiddenHardCoreColoring.Mixing

/-- **Lemma 10** (Xiongxin Yang, STOC 2027 submission #964 (October 2026), p.11). For distinct non-adjacent `u, v` and every `f`,
`0 ≤ ∑_c ⟨Q_{u,c} f, Q_{v,c} f⟩_µ ≤ (1 + 2/(q − Δ))⟨Q_u f, Q_v f⟩_µ`. -/
theorem lemma_10 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ q : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (hq : Δ + 3 ≤ q) (u v : V) (huv : u ≠ v) (hnadj : ¬ G.Adj u v) (f : Col G q → ℝ) :
    0 ≤ ∑ c : Fin q, ip G q (Qvc G q u c *ᵥ f) (Qvc G q v c *ᵥ f) ∧
      ∑ c : Fin q, ip G q (Qvc G q u c *ᵥ f) (Qvc G q v c *ᵥ f) ≤
        (1 + 2 / ((q : ℝ) - (Δ : ℝ))) * ip G q (Qv G q u *ᵥ f) (Qv G q v *ᵥ f) := by sorry

end HiddenHardCoreColoring.Mixing
