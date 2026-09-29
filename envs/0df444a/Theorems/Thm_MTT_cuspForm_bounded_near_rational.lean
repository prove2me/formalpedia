-- Prove2me | Theorems.Thm_MTT_cuspForm_bounded_near_rational
-- name    : MTT.cuspForm_bounded_near_rational
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-07T13:13:58.873085+00:00
-- url     : https://prove2.me/theorems/307607be-3ed8-41b6-9442-b71f16c90c1d
-- title:
--   A cusp form is bounded on the vertical segment above a rational cusp
-- statement:
--   A cusp form of level $\Gamma_1(N)$ is bounded on the vertical segment running from a rational point up to height one.
--
--   Precisely: for $f \in S_k(\Gamma_1(N))$ and $r \in \mathbf Q$ there is a constant $C$ with
--   $$|f(r+it)| \le C \qquad \text{for all } 0 < t \le 1 .$$
--
--   This is the statement that $f$ does not blow up as the vertical ray descends to the rational point $r$, which is a cusp of $\Gamma_1(N)$. It is the delicate half of the assertion that the Mazur–Tate–Teitelbaum modular integral
--   $$\int_0^\infty f(r+it)\,P(r+it)\,dt$$
--   converges: convergence at the top of the ray is the exponential decay of $f$ at the cusp $\infty$, which is immediate from the $q$-expansion, while convergence at the bottom is exactly this statement.
--
--   **Why boundedness is not automatic.** The Petersson bound $|f(z)| \ll (\operatorname{Im} z)^{-k/2}$, valid for any cusp form, gives only $|f(r+it)| \ll t^{-k/2}$, which is unbounded for $k \ge 1$ and not integrable near $t=0$ for $k \ge 2$. The bound stated here therefore genuinely uses the vanishing of $f$ at the cusp $r$, not merely its modularity. Writing $r = \sigma\cdot\infty$ with $\sigma = \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in \mathrm{SL}_2(\mathbf Z)$, one has $\sigma^{-1}(r+it) = -d/c + i/(c^2 t)$, so that
--   $$f(r+it) = (i/(ct))^{k}\,\big(f|_k\sigma\big)\!\left(-\tfrac{d}{c} + \tfrac{i}{c^2t}\right),$$
--   and the imaginary part on the right tends to $+\infty$ as $t \to 0^+$. Since $f|_k\sigma$ vanishes at $\infty$ — and, being invariant under $\Gamma(N)$, which is normal in $\mathrm{SL}_2(\mathbf Z)$, is periodic of period $N$ and so decays like $e^{-2\pi \operatorname{Im}(\cdot)/N}$ — the exponential factor $e^{-2\pi/(Nc^2 t)}$ overwhelms the pole $t^{-k}$. In fact $f(r+it) \to 0$ as $t \to 0^+$; only boundedness is asserted here, since that is what the integrability argument consumes.
--
--   **Formalization note.** `UpperHalfPlane.ofComplex` is the section of the inclusion $\mathbf H \hookrightarrow \mathbf C$ that takes an arbitrary junk value off the upper half-plane; for $t > 0$ the point $r+it$ lies in $\mathbf H$, so `ofComplex` returns it and the statement says what it appears to say.
-- source:
--   Mazur-Tate-Teitelbaum, On p-adic analogues of the conjectures of Birch and Swinnerton-Dyer, Invent. Math. 84 (1986), I.§1-2; Shimura, Introduction to the arithmetic theory of automorphic functions, Ch. 2 and Ch. 8; Diamond-Shurman, A First Course in Modular Forms, §1.2 and §5.9.

import Definitions.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.cuspForm_bounded_near_rational
    {N k : ℕ} (hN : 0 < N) (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (r : ℚ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖f (UpperHalfPlane.ofComplex ((r : ℂ) + Complex.I * t))‖ ≤ C := by sorry
