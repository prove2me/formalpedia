-- Prove2me | Theorems.Thm_MasulloGRH_mellin_iso_expDecay_rpos
-- name    : MasulloGRH.mellin_iso_expDecay_rpos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:34:02.958185+00:00
-- url     : https://prove2.me/theorems/aedd4da1-89d6-4185-9c8d-8a3d67869b2a
-- title:
--   Proposition D.3.2.5 — the Mellin transform is a topological isomorphism $\mathcal S_I(\mathbb R_{>0})\to AS(\mathbb C_I)$
-- statement:
--   Let $I\subset\mathbb R$ be a non-empty open interval. Let $\mathcal S_I(\mathbb R_{>0})$ be the space of smooth functions $\phi$ on $\mathbb R_{>0}$ with $t^a\phi\in\mathcal S(\mathbb R_{>0})$ for all $a\in I$, with its projective topology, and let $AS(\mathbb C_I)$ be the Schwartz–Bergman space of holomorphic functions on the strip $\mathbb C_I=\{\operatorname{Re}s\in I\}$ that are Schwartz uniformly on vertical substrips of bounded width.
--
--   For $\phi\in\mathcal S_I(\mathbb R_{>0})$ and $\operatorname{Re}(s)\in I$ the Mellin integral
--   $$M(\phi)(s)=\int_0^\infty\phi(t)\,t^s\,\frac{dt}{t}$$
--   converges absolutely, the function $M(\phi)$ belongs to $AS(\mathbb C_I)$, and
--
--   $$M_I\colon\mathcal S_I(\mathbb R_{>0})\longrightarrow AS(\mathbb C_I),\qquad\phi\mapsto M(\phi),$$
--
--   is a linear topological isomorphism.
--
--   This is the Paley–Wiener theorem that identifies functions of prescribed exponential decay on $\mathbb R_{>0}$ with holomorphic functions on a vertical strip.
--
--   **Formalization Note** An interval is an order-connected set. The integral is written in the coordinate $t=e^x$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, §D.3.2, Proposition D.3.2.5 (Fourier-Mellin transform on S_I(R_{>0})), eq. (D.3.2.2), p. 802

import Definitions.Def_MasulloGRH_ExpDecaySpaces

set_option autoImplicit false

namespace MasulloGRH

theorem mellin_iso_expDecay_rpos (I : Set ℝ) (hI : IsOpen I) (hI' : I.OrdConnected)
    (hne : I.Nonempty) :
    ∃ M : ExpDecaySchwartzRpos I →ₗ[ℂ] SchwartzBergman I,
      IsLinearTopologicalIso M ∧
      ∀ (ϕ : ExpDecaySchwartzRpos I) (s : ℂ), s.re ∈ I →
        MeasureTheory.Integrable
          (fun x : ℝ => ϕ.toFun (Multiplicative.ofAdd x) * Complex.exp (s * x)) ∧
        (M ϕ).toFun s = ϕ.mellin s := by sorry

end MasulloGRH
