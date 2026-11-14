-- Prove2me | Theorems.Thm_LatticePrepro_hankel_reconstruction
-- name    : LatticePrepro.hankel_reconstruction
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:05.36521+00:00
-- url     : https://prove2.me/theorems/a0e74629-509a-4803-883b-a3163a62b715
-- title:
--   Theorem A.7 — moment reconstruction from a Hankel matrix with Frobenius identities
-- statement:
--   Let $p$ be a prime and let $\Omega$ be an algebraically closed field that is an $\mathbb{F}_p$-algebra (so of characteristic $p$). Let $r\ge2$ be an integer and $\ell=p(r-1)+1$. Let $(y_k)_{k\ge0}$ be a sequence in $\Omega$ satisfying the Frobenius identities
--   $$y_{pk}=y_k^{\,p}\qquad\text{whenever } pk\le2\ell-2 .$$
--   Let $t<r$, and suppose that the first $t+1$ columns of the Hankel matrix $(y_{i+j})_{0\le i,j<\ell}$ are linearly dependent over $\Omega$: there are $c_0,\dots,c_t\in\Omega$, not all zero, with
--   $$\sum_{j=0}^{t}c_j\,y_{i+j}=0\qquad(0\le i<\ell).$$
--   Then there is a finitely supported coefficient function $f\colon\Omega\to\mathbb{F}_p$ with $|\mathrm{supp}\,f|\le t$ and
--   $$y_k=\mu_k(f)=\sum_{\alpha\in\Omega}f(\alpha)\,\alpha^k\qquad(0\le k<\ell).$$
--
--   This is the reconstruction step behind the soundness of the explicit tables. In Theorem A.8 it is applied to the moments $y_k=\hat\mu_k(y)$ of a light evaluation table satisfying the constraints, whose Hankel matrix has small rank by Lemma A.6, and shows that the table represents a sparse coefficient function.
--
--   **Formalization Note**: The paper takes the $y_k$ in a finite field $K$, assumes $\operatorname{rank}_K(y_{i+j})_{i,j<\ell}=t<r$, and obtains $f$ on some finite extension of $K$. The Lean version works directly in a fixed algebraically closed field $\Omega$ (later Mathlib's `AlgebraicClosure K`) and only assumes that the first $t+1$ Hankel columns are dependent, which follows from rank $\le t$ since $t+1\le\ell$; it is therefore a slight generalization. The sequence is a function `ℕ → Ω`, of which only $y_0,\dots,y_{2\ell-2}$ matter. Coefficient functions are `Ω →₀ ZMod p`, and $\mu_k$ uses the convention $0^0=1$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Theorem A.7 (\label{thm:moment-hankel-reconstruction}); Lean: LatticePrepro/Tables/Hankel.lean, LatticePrepro.hankel_reconstruction

import Mathlib
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Tables_Hankel

open LatticePrepro
open Polynomial

theorem LatticePrepro.hankel_reconstruction {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω]
    [Algebra (ZMod p) Ω] [IsAlgClosed Ω] {r : ℕ} (hr : 2 ≤ r) (y : ℕ → Ω)
    (hfrob : ∀ k, p * k ≤ 2 * hankelLen p r - 2 → y (p * k) = y k ^ p)
    {t : ℕ} (ht : t < r)
    (hdep : ∃ c : Fin (t + 1) → Ω, c ≠ 0 ∧
      ∀ i : Fin (hankelLen p r), ∑ j, c j * y (i.val + j.val) = 0) :
    ∃ f : Ω →₀ ZMod p, f.support.card ≤ t ∧ ∀ k < hankelLen p r, y k = moment f k := by sorry
