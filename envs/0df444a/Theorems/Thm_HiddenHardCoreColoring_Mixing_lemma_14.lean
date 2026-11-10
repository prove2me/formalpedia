-- Prove2me | Theorems.Thm_HiddenHardCoreColoring_Mixing_lemma_14
-- name    : HiddenHardCoreColoring.Mixing.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T09:00:23.375489+00:00
-- url     : https://prove2.me/theorems/4dd6d197-7a85-4641-9069-afb9112a2ac7
-- title:
--   Lemma 14 — mean–variance identity ⟨f, L_c f⟩ = M_c(f) + V_c(f)
-- statement:
--   Throughout, $G=(V,E)$ is a finite simple graph on $n=|V|\ge1$ vertices with $\deg(v)\le\Delta$ for every $v$, $[q]=\{0,\dots,q-1\}$ is the palette, $\Omega$ is the set of proper $q$-colorings, $\mu$ is uniform on $\Omega$, and $q\ge\Delta+3$ (the standing assumption of §§3.2–7). For every color $c$ and every $f\in L^2(\mu)$,
--   $$\langle f,L_cf\rangle_\mu=M_c(f)+V_c(f),$$
--   with $M_c(f)=\sum_v\mathbb E_\mu[\mathbf 1\{\sigma_v=c\}(1-p_v)(f-E_v^{-c}f)^2]$ and $V_c(f)=\sum_v\mathbb E_\mu[\mathbf 1\{\sigma_v=c\}(1-p_v)\mathrm{Var}_v^{-c}f]$.
--
--   **Formalization Note** Functions on $\Omega$ are all real functions on the subtype of proper colorings; operators are matrices on $\Omega$ acting by $(Mf)(\sigma)=\sum_\tau M(\sigma,\tau)f(\tau)$, and $\langle f,g\rangle_\mu$ is the uniformly weighted sum.
--
--   Differences from the source: none.
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; Lemma 14, p.17

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_Coloring

open Finset Matrix

namespace HiddenHardCoreColoring.Mixing

/-- **Lemma 14** (Xiongxin Yang, STOC 2027 submission #964 (October 2026), p.17). For every color `c` and every `f`, `⟨f, L_c f⟩_µ = M_c(f) + V_c(f)`. -/
theorem lemma_14 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ q : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (hq : Δ + 3 ≤ q) (c : Fin q) (f : Col G q → ℝ) :
    ip G q f (Lc G q c *ᵥ f) = Mc G q c f + Vc G q c f := by sorry

end HiddenHardCoreColoring.Mixing
