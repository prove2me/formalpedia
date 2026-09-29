-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_FinWhittakerDatum_exists_norm_Wf_globalPoints_diagOne_mul_le
-- name    : LanglandsTunnell.Converse.FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/d8bcbb0c-50e5-5d17-8c25-da90f3c5d03e
-- title:
--   Polynomial bound for finite Whittaker values on the rational torus
-- statement:
--   Let $K$ be a number field, $S$ a finite set of finite places of $K$, and $\Pi$ a Hecke eigensystem over $K$ with complex values, i.e. a non-zero level ideal of $\mathcal O_K$ together with families $a_v, b_v \in \mathbb C$ indexed by the finite places. Assume $\Pi$ grows at most polynomially outside $S$: for some real $\kappa_0$ one has $\|a_v\| \le (\mathrm{N}v)^{\kappa_0}$ and $\|b_v\| \le (\mathrm{N}v)^{\kappa_0}$ for all $v \notin S$, $\mathrm{N}v$ the absolute norm of $v$. Let $D$ be a finite Whittaker datum for $(S,\Pi)$, that is a function $W_f$ on $\mathrm{GL}_2(\mathbb A_K)$ factoring through the finite part, right invariant under $\mathrm{GL}_2(K_v)$ for $v \in S$, transforming on the left under unipotents at $v \notin S$ by the local additive character `psiLocal`, right invariant under $\mathrm{GL}_2(\mathcal O_v)$ for $v \notin S$, a Hecke coset eigenfunction with eigenvalue $a_v$ at every $v \notin S$ for all levels prime to $v$, satisfying the central relation with eigenvalue $(\mathrm{cNorm}\,v)^{-1} b_v$ at $v \notin S$, and right invariant under the level subgroup of some non-zero ideal intersected with the finite-adelic subgroup. Let $g \in \mathrm{GL}_2(\mathbb A_K)$ and let integers $n_v$ be given for $v \in S$. Then there exist a non-zero $\delta \in \mathcal O_K$ and reals $C$ and $\kappa \ge 0$ such that for every $\alpha \in K^\times$ with $|\alpha|_v \le \exp(n_v)$ for all $v \in S$ (so the order of $\alpha$ at $v$ is at least $-n_v$) and with $W_f(\mathrm{diag}(\alpha,1)\,g) \ne 0$, the product $\delta\alpha$ lies in $\mathcal O_K$, say $\delta\alpha = \beta$, and $\|W_f(\mathrm{diag}(\alpha,1)\,g)\| \le C\,|N_{K/\mathbb Q}(\beta)|^{\kappa}$, where $\mathrm{diag}(\alpha,1)$ denotes the rational torus point embedded into $\mathrm{GL}_2(\mathbb A_K)$.
--
--   This is the arithmetic input to the converse-theorem construction: for a fixed adelic point $g$, the torus values of a finite Whittaker datum vanish outside a lattice of $\alpha$'s and are bounded by a fixed power of the norm of the corresponding integer. It is used in the cusp-synthesis step, where growth exponents, local majorants, the torus transform against a Haar measure, and $L^p$-membership of translated sums are established.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_FinWhittakerDatum_exists_norm_Wf_globalPoints_diagOne_mul_le.lean

import Definitions.Def_LanglandsTunnell_JLConverse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm NumberField.AdelicLevel
open LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.FinWhittakerDatum.exists_norm_Wf_globalPoints_diagOne_mul_le (K : Type) [Field K]
    [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (Pi : HeckeEigensystem K ℂ)
    (hgrow : ∃ κ : ℝ, ∀ v ∉ S,
      ‖Pi.a v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ ∧ ‖Pi.b v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ)
    (D : FinWhittakerDatum K S Pi) (g : AdelicGL2 (𝓞 K) K) (n : ↥S → ℤ) :
    ∃ δ : 𝓞 K, δ ≠ 0 ∧ ∃ C κ : ℝ, 0 ≤ κ ∧ ∀ α : Kˣ,
      (∀ v : ↥S, Valued.v ((localOf K v.1 α : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
        ≤ WithZero.exp (n v)) →
      D.Wf (globalPoints (𝓞 K) K (diagOne α) * g) ≠ 0 →
        ∃ β : 𝓞 K, (β : K) = (δ : K) * (α : K) ∧
          ‖D.Wf (globalPoints (𝓞 K) K (diagOne α) * g)‖ ≤ C * |Algebra.norm ℚ (β : K)| ^ κ := by sorry
