-- Prove2me | Theorems.Thm_NesterovODE_GenScheme_z_identity
-- name    : NesterovODE.GenScheme.z_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:51:00.061615+00:00
-- url     : https://prove2.me/theorems/ef56c76d-9794-421c-8340-a164c248e420
-- title:
--   p. 15, proof of Theorem 6 — z_{k−1} − s(k + r − 2)G_s(y_{k−1})/(r − 1) = z_k
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $g:\mathcal H\to\mathbb R$, $s>0$, $r>3$, and let $P:\mathcal H\to\mathcal H$ be any map. Let $(x_k)$ be a run of the generalized Nesterov scheme (19) with parameter $r$, step $s$ and proximal map $P$, with extrapolated points $y_k$ ($y_0=x_0$), and put $G_s(y)=\big(y-P(y-s\nabla g(y))\big)/s$ and
--
--   $$
--   z_k=\frac{k+r-1}{r-1}\,y_k-\frac{k}{r-1}\,x_k = x_k+\frac{k-1}{r-1}(x_k-x_{k-1})\quad(k\ge1),\qquad z_0=x_0 .
--   $$
--
--   Then for every $k\ge1$,
--
--   $$
--   z_{k-1}-\frac{s(k+r-2)}{r-1}\,G_s(y_{k-1}) = z_k .
--   $$
--
--   This identity turns the inner-product term produced by the basic proximal-gradient inequality into a difference of squared distances $\|z_{k-1}-x^\star\|^2-\|z_k-x^\star\|^2$, which is what makes the discrete energy of Theorem 6 telescope.
--
--   **Formalization Note.** $z_k$ is the published `NesterovFB.Rates.zSeq r x k` $=x_k+\frac{k-1}{r-1}(x_k-x_{k-1})$, which equals the paper's $(k+r-1)y_k/(r-1)-kx_k/(r-1)$ by (19), and equals $x_0$ at $k=0$. The hypothesis $r>3$ is the standing assumption of §4.1 (the identity itself only needs $r>1$); nothing about $g$, $h$ or $P$ is needed.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 15, proof of Theorem 6 (first line)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_NesterovFB_Rates_Algorithm
import Definitions.Def_NesterovODE_GenScheme_Run

open InnerProductSpace NesterovFB.Rates ThreeOpSplitting.ConvexRates

namespace NesterovODE.GenScheme

theorem z_identity {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (s r : ℝ) (P : H → H) (x : ℕ → H)
    (hs : 0 < s) (hr : 3 < r)
    (hrun : IsGenNesterovRun Φ P r s x) :
    ∀ k : ℕ, 1 ≤ k →
      zSeq r x (k - 1) - (s * ((k : ℝ) + r - 2) / (r - 1)) • gradMap Φ P s (extrap r x (k - 1))
        = zSeq r x k := by sorry

end NesterovODE.GenScheme
