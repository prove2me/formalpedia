-- Prove2me | Theorems.Thm_MTT_Cohomology_integral_class_character_law
-- name    : MTT.Cohomology.integral_class_character_law
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-06T15:49:33.209414+00:00
-- url     : https://prove2.me/theorems/804bcccd-e8d1-4bbf-b71f-f57e0ec09044
-- title:
--   Nebentype law for the modular symbol of an eigenform
-- statement:
--   Let $f$ be a normalized algebraic cuspidal Hecke eigenform of weight $k \ge 2$ and level $N > 0$,
--   with nebentypus $\varepsilon$, so that for every $\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\Gamma_0(N)$
--   $$f(\gamma z)=\varepsilon(d)\,(cz+d)^{k}\,f(z).$$
--   Let $\varphi$ be a compactly supported cohomology class of weight $n=k-2$ whose coefficient functionals
--   compute the modular integrals of $f$, that is
--   $$\bigl\langle \varphi([\infty]-[r]),\ X^{j}Y^{\,k-2-j}\bigr\rangle
--   = \binom{k-2}{j}\,\int_{r}^{i\infty} f(z)\,z^{j}\,dz \quad (0\le j\le k-2,\ r\in\mathbf Q),$$
--   in the normalization fixed by `IntegralClass`. Then $\varphi$ obeys the corresponding nebentype law
--   in cohomology: for every $\gamma\in\Gamma_0(N)$ and all cusps $x,y$,
--   $$\varphi(\gamma x,\gamma y)=\varepsilon(d)\cdot\bigl(\gamma\cdot\varphi(x,y)\bigr),$$
--   where $\gamma$ acts on binary forms of degree $k-2$ by $P(X,Y)\mapsto P\bigl((X,Y)\gamma\bigr)$ and
--   $\varepsilon(d)$ is transported to $\mathbf C$ along the fixed embedding $\iota$.
--
--   The class $\varphi$ is determined by the displayed integrals: the values on the paths $[\infty]-[r]$
--   determine all values by the cocycle relation, and a binary form of degree $k-2$ is determined by its
--   $k-1$ coefficients. So the statement is not an extra axiom but a *theorem* about the modular integral —
--   and it is exactly the point where analysis enters. Proving it requires the transformation behaviour of
--   the path integral $\int_{r}^{i\infty}f(z)P(z)\,dz$ under $z \mapsto \gamma z$: the substitution
--   turns the vertical ray into a circular arc, so the identity rests on the holomorphy of $f$ and the
--   homotopy invariance of contour integrals in the upper half-plane, together with the rapid decay of a
--   cusp form at the cusps.
--
--   This is the standard bridge from the automorphy of $f$ to the $\Gamma_0(N)$-equivariance of its modular
--   symbol, and it is what upgrades a class satisfying only the Hecke relations to a full eigenpacket.
-- source:
--   Mazur-Tate-Teitelbaum, On p-adic analogues of the conjectures of Birch and Swinnerton-Dyer, Invent. Math. 84 (1986), 1-48, I.§1-§2 and (8.6); Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Ch. 8; Ash-Stevens, Modular forms in characteristic l and special values of their L-functions (1986), §4, https://math.bu.edu/people/ghs/papers/Mod_fms_char_ell.pdf.

import Definitions.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.integral_class_character_law
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (φ : Hc N (k-2) ℂ) (hφ : IntegralClass f.form φ)
    (γ : CongruenceSubgroup.Gamma0 N) (x y : Cusp) :
    φ.val (cuspAct γ.val x, cuspAct γ.val y)
      = ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val (φ.val (x, y)) := by sorry
