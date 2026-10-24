-- Prove2me | Theorems.Thm_K24_Global_full_fixed_reference_change_of_slice
-- name    : K24.Global.full_fixed_reference_change_of_slice
-- status  : Open
-- author  : @xwh
-- created : 2026-10-23T08:59:29.614722+00:00
-- url     : https://prove2.me/theorems/aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22
-- title:
--   Full K24: geometric change of slice, inverse transfer and regularity sharpness
-- statement:
--   This problem asks for a **formal proof of the complete conditional geometric K24 change-of-slice result**, including its regularity obstruction. The source gives informal analytic arguments; this publication does not claim a new proof or a new unsolved conjecture for the standard perturbation lemma. It does not assert existence of the still-missing geometric organizer in the four-dimensional Einstein research program.
--
--   Let $M$ be a closed smooth real four-manifold with an actual common smooth circle action. Write $\Pi_0$ for its normalized Haar average on the relevant tensor, covector, or vector bundle and $\Pi_\perp=I-\Pi_0$. Let the positive metrics $\widehat g$ and $z$ be invariant under that same action; the actual nearby positive metric $g$ need not be invariant. The scalar $\lambda$ is arbitrary. Define
--   $$E(q)=\operatorname{Ric}_q-\lambda q,\qquad
--   \Psi_{\widehat g}(q)=E(q)+\delta_q^*\Pi_\perp\beta_{\widehat g}(q-\widehat g),$$
--   where $\beta_h u=-\operatorname{div}_h u+\tfrac12d\operatorname{tr}_h u$, $\delta_h^*$ is the symmetrized covariant derivative with factor $1/2$, and $\mathcal K_hY=\mathcal L_Yh$. These are actual geometric differential operators, not freely supplied linear maps.
--
--   Fix the numerical data for a uniformly bounded local finite-cover system, metric ellipticity and coefficient bounds, $0<\alpha<1$, and a uniform pullback bound $H\ge1$ for the common action. **These bounds are fixed before the conclusion constants are chosen.** Covering degree is not globally bounded, and the downstairs overlap count is kept separate from the internal coordinate atlas on each covering manifold. The proposition requires all of the following.
--
--   1. **Exact tensor identities and genuine differentiation.** Prove the full product rule
--   $$D\Psi_{\widehat g}(z)u=DE(z)u+(D\delta^*)_z[u]\,\Pi_\perp\beta_{\widehat g}(z-\widehat g)+\delta_z^*\Pi_\perp\beta_{\widehat g}u.$$
--   Invariance makes the middle term vanish. On the genuine zero-Haar-mean tensor sector, identify the difference of the fixed-reference and re-anchored derivatives as
--   $$R_{\widehat g,z}u=\delta_z^*(\beta_{\widehat g}-\beta_z)u.$$
--   The target also includes the actual connection/Bianchi coefficient expansions, principal-symbol identification by a quadratic-jet test and its intrinsic norm bound, sector preservation and equivariance. It requires the displayed variation to be the **Fréchet derivative in the specified section norms on a positive-radius metric neighborhood**, not just a pointwise or directional derivative.
--
--   2. **Uniform tensor estimates in both scales.** For one uniform $C_T$,
--   $$\|R_{\widehat g,z}u\|_{C^{0,\alpha}_{\rm cov}}
--   \le C_T\|\widehat g-z\|_{C^{2,\alpha}_{\rm cov}}\|u\|_{C^{2,\alpha}_{\rm cov}}.$$
--   For every real $s>4$, with the corresponding fixed local Sobolev coefficient/atlas bounds, require a uniform $C_S$ with
--   $$\|R_{\widehat g,z}u\|_{H^{s-2}_{\rm cov}}
--   \le C_S\|\widehat g-z\|_{H^s_{\rm cov}}\|u\|_{H^s_{\rm cov}}.$$
--   The Sobolev clause is not restricted to integer order and does not impose higher Hölder regularity on the metric. It uses local real-order metric and inverse-metric bounds; it does not impose a fixed global bound on the degree-dependent norm of the whole metric.
--
--   3. **Both vector errors and the correct regularity.** For the actual projected operator $B_{\widehat g,g}Y=\Pi_\perp\beta_{\widehat g}\mathcal L_Yg$, retain both terms:
--   $$B_{\widehat g,g}-B_{z,z}=\Pi_\perp\big[(\beta_{\widehat g}-\beta_z)\mathcal K_z+
--   \beta_{\widehat g}\mathcal L_{(\cdot)}(g-z)\big].$$
--   Prove the natural $C^{2,\alpha}\to C^{0,\alpha}$ estimate by a uniform constant times
--   $(\|\widehat g-z\|_{C^{2,\alpha}}+\|g-z\|_{C^{2,\alpha}})\|Y\|_{C^{2,\alpha}}$.
--   For the shifted $C^{3,\alpha}\to C^{1,\alpha}$ pair, both metric differences must instead be controlled in $C^{3,\alpha}$. The actual Bianchi–Killing/rough-Laplacian identity is also included.
--
--   4. **Geometric inverse transfer.** In each stated pair of actual zero-mean section spaces, suppose the re-anchored projected operator is a bounded linear isomorphism with inverse bound $C_A$ (or $C_B$). If that bound times the norm of the actual difference operator is strictly below $1/2$, prove that the fixed-reference operator is an isomorphism with inverse bound at most $2C_A$ (respectively $2C_B$), including surjectivity and the corresponding Banach-dual gap. Mere absence of kernel is not substituted for the initial isomorphism. Norm, completeness, Haar integrability/boundedness and projection facts needed for this argument are requested conclusions about the concrete spaces; they are not assumed copies of the desired theorem.
--
--   5. **Actual flat-torus sharpness.** On the genuine four-torus with coordinates of period $2\pi$, use the flat metric, the circle translation in $x_2$, $V=\cos(x_2)\partial_{x_1}$ and
--   $$f_n=n^{-(3+\alpha)}\sin(nx_1)(dx_1\otimes dx_1).$$
--   Require positivity of $g_n=g_0+f_n$ for $n\ge2$, finite norms, $\|f_n\|_{C^{2,\alpha}}\to0$, bounded $C^{3,\alpha}$ norms, and a lower bound $\pi^{-\alpha}$ for the $C^{1,\alpha}$ norm of the projected actual vector-operator difference tested on $V$. Consequently no uniform shifted estimate using only the $C^{2,\alpha}$ metric difference can hold. This is a statement about genuine torus tensors and operators, not an abstract sequence of scalar exponents.
--
--   **Norm and formalization choices.** The definition packages specify full big Hölder norms from actual iterated derivatives and top-order Hölder seminorms, hierarchical local finite covers, and real-order Bessel–Sobolev norms with explicit partitions. Sobolev carriers use the continuous/C² representatives justified by the requested ranges; their completeness and norm properties remain to be proved. The adapted Sobolev norm is an explicit upstairs sum and is not identified with downstairs $L^2$ independently of covering degree. Haar averaging is pointwise in finite-dimensional fibers, avoiding an unsupported assumption of norm-continuous action on big Hölder space. The projection bounds are $H$ and $1+H$; $1$ and $2$ apply only in the isometric case. Raw inverse, derivative and integral definitions are totalized in Lean, while positivity, regularity, integrability and the analytic properties are enforced by the full statement's hypotheses or required conclusions. Definitions have no admissions or new axioms. There is exactly one intentional unproved theorem placeholder.
--
--   **Remaining application boundary.** K24 does not construct the common marked action, the required same-window $C^2$/$C^3$ closeness, or the adapted re-anchored inverse from an arbitrary Einstein degeneration. Those organizer inputs remain open. The nonlinear diffeomorphism-chart and quadratic-remainder applications in K16/K21 are separate supporting questions; they require their own loss-aware regularity hypotheses/proofs. Neither those applications nor the original Einstein conjecture is claimed proved by this publication.
--
--   Source: `liushuijixiang/siwei-einstein`, commit `8c02be189f097080feca952347c9104bfb986242`, `四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md`, §§1–7, with K16/K21/K23 for the inherited closed-manifold, cover, action and inverse conventions. Eleven source files were checked against their Git blob hashes. Independent Astra Ultra definition readback and source comparison approved the full statement's meaning. Scoped local compilation passed with the sole expected unproved-target warning; this is not a proof acceptance.
--
--
--   **Description correction (24 October 2026).** The explicit torus example above now agrees with source §5.1, equations (5.6)–(5.8) and the unchanged formal definitions: the perturbation is in the $dx_1\otimes dx_1$ component and the test vector is $\cos(x_2)\partial_{x_1}$. Earlier prose incorrectly described a cross component and a sine test vector. The Lean statement and its hypotheses are unchanged.
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — full §§1–7; inherited conventions in K16/K21/K23. Explicit norm choices and still-open organizer recorded in natural-language statement.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false

namespace K24.Global
universe u
theorem full_fixed_reference_change_of_slice : FullK24Statement.{u} := by
  sorry
end K24.Global
