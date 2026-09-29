-- Prove2me | Theorems.Thm_GrothendieckConstant_krivine_scheme_affine_constraint
-- name    : GrothendieckConstant.krivine_scheme_affine_constraint
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-23T18:43:08.734577+00:00
-- url     : https://prove2.me/theorems/ce6a31ee-d61e-4951-95cf-e878e3befca2
-- title:
--   Theorem 2.2, eq. (1): $b_3\ge2b_1-\tfrac{11}{6}$
-- statement:
--   **Theorem 2.2 of the source, equation (1).** Let $f,g:\mathbb R^k\to\{\pm1\}$ be measurable odd functions — a Krivine scheme of dimension $k$ — and let
--
--   $$H(t)=\frac{\pi}{2}\mathbb E[f(X)g(Y)]=b_1t+b_3t^3+\cdots$$
--
--   be its normalized correlation function, where $X,Y$ are standard Gaussian vectors in $\mathbb R^k$ with $\mathbb E[X_iY_i]=t$. Then the two leading coefficients obey the affine constraint
--
--   $$b_3\ \ge\ 2b_1-\frac{11}{6}.$$
--
--   The constraint holds in every dimension $k$. It is tight at the hyperplane scheme, where $H(t)=\arcsin t$ and $(b_1,b_3)=(1,\tfrac16)$, so no scheme can push its linear coefficient up without paying in its cubic coefficient. Because the constraint is affine in $(b_1,b_3)$, and those coefficients are linear functionals of the scheme, it passes automatically to mixtures of schemes and to coefficientwise limits — which is what allows it to be converted into a lower bound on $K_G$.
--
--   **Formalization Note** $b_1$ and $b_3$ are taken to be $H'(0)$ and $H'''(0)/6$. Oddness of $f$ and $g$ is imposed almost everywhere, since a $\pm1$-valued function cannot be odd at the origin; the half-space scheme witnesses that schemes exist in every dimension $k\ge1$.
-- source:
--   Li, Saha, Xue, Chaudhuri, Klivans, Kothari, Meka, "Long-Horizon AI Research for Grothendieck Constant: A Case Study in Human-AI Mathematical Collaboration", arXiv:2608.11195v3 (2026), https://arxiv.org/abs/2608.11195, Section 2, p. 6, Theorem 2.2 (Lower bound, abridged), equation (1): "The correlation function H(t) = b1 t + b3 t^3 + ... of every Krivine scheme satisfies the constraint b3 >= 2 b1 - 11/6." Full proof in the companion paper, Saha et al., "New upper and lower bounds for the Grothendieck constant" (2026), Part 1.

import Mathlib
import Definitions.Def_KrivineSchemeDefs

namespace GrothendieckConstant

theorem krivine_scheme_affine_constraint (k : ℕ) (S : KrivineScheme k) :
    2 * coeffLinear S - 11 / 6 ≤ coeffCubic S := by sorry

end GrothendieckConstant
