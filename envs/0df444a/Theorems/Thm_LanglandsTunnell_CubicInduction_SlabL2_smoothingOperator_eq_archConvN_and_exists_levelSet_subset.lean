-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_smoothingOperator_eq_archConvN_and_exists_levelSet_subset
-- name    : LanglandsTunnell.CubicInduction.SlabL2.smoothingOperator_eq_archConvN_and_exists_levelSet_subset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/b3af7deb-60d5-5f78-875b-79b975488321
-- title:
--   Smoothing operators as archimedean convolutions; level sets near 1
-- statement:
--   Two assertions about $\mathrm{GL}_3$ over the adeles of $\mathbb{Q}$ are combined. (i) Let $\alpha\colon(\mathrm{Fin}\,3\to\mathrm{Fin}\,3\to\mathbb{R})\to\mathbb{C}$, let $K'$ assign to each height-one prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ a subgroup $K'_p\le \mathrm{GL}_3$ of the $p$-adic completion of $\mathbb{Q}$, and let $\varphi,f\colon\mathrm{GL}_3(\mathbb{A})\to\mathbb{C}$. Assume: $\alpha$ is $C^\infty$ on the $3\times 3$ real arrays, has compact support, and its topological support lies in the arrays of nonzero determinant; each $K'_p$ is open and compact as a subset; $K'_p$ equals the subgroup `localMaximalCompact3` (matrices whose entries and whose inverse's entries all have valuation $\le 1$) for all but finitely many $p$; $\varphi(g)=\alpha(\mathrm{archEntries}\,g)$ times the indicator at $g$ of $\{x\mid \forall p,\ x_p\in K'_p\}$, where $\mathrm{archEntries}\,g$ records the real-place coordinates of the entries of the archimedean component of $g$; and $f$ is continuous. Then there are a continuous $\Psi$ and a real $N>0$ with $\int \varphi(g) f(xg)\,dg = \int_{\mathrm{GL}_3(\mathbb{Q}_\infty)} \Psi(x\cdot h)\,\alpha(\mathrm{kernelEnt}\,h)\,dh$ for all $x$ (Haar measures on $\mathrm{GL}_3(\mathbb{A})$ and on $\mathrm{GL}_3$ of the infinite adeles, $h$ included adelically), and such that for every $y$ and every real $\varepsilon$: if $\|f(yk)-f(y)\|\le\varepsilon$ for all $k\in\mathrm{GL}_3(\mathbb{A}^f)$ with $k_p\in K'_p$ for all $p$, then $\|\Psi(y)-N f(y)\|\le \varepsilon N$. (ii) Every neighbourhood $V$ of $1$ in $\mathrm{GL}_3(\mathbb{A}^f)$ contains the level set $\{k\mid \forall p,\ k_p\in K'_p\}$ of some such family $K'$ of open compact subgroups agreeing cofinitely with `localMaximalCompact3`.
--
--   This is the analytic input identifying convolution against a factorisable smoothing kernel on $\mathrm{GL}_3(\mathbb{A})$ with an archimedean convolution of the finite-adelic level average of $f$, together with the statement that level sets of level data form a neighbourhood basis of the identity in $\mathrm{GL}_3(\mathbb{A}^f)$. It is used in the step deducing that a function annihilated in the appropriate sense by all smoothing kernels is an eigenvector for the Casimir action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_smoothingOperator_eq_archConvN_and_exists_levelSet_subset.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2KernelCasimir
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.CubicInduction
  LanglandsTunnell.CubicInduction.SlabL2

theorem LanglandsTunnell.CubicInduction.SlabL2.smoothingOperator_eq_archConvN_and_exists_levelSet_subset :
    (∀ (α : (Fin 3 → Fin 3 → ℝ) → ℂ) (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)))
        (φ f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      IsSmoothArchFactor α →
      (∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧ IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ)))) →
      (∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) →
      (∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, φ g = α (archEntries g) *
        Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) g) →
      Continuous f →
      ∃ (Ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (N : ℝ), Continuous Ψ ∧ 0 < N ∧
        (∀ x, smoothingOperator φ f x = archConvN (Fin 3) ℚ Ψ (fun h => α (kernelEnt h)) x) ∧
        ∀ (y : AdelicGL 3 (𝓞 ℚ) ℚ) (ε : ℝ),
          (∀ k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ), (∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p) →
            ‖f (y * finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) - f y‖ ≤ ε) →
          ‖Ψ y - N * f y‖ ≤ ε * N) ∧
    (∀ V ∈ nhds (1 : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)),
      ∃ K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)),
        (∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧ IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ)))) ∧
        (∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
        {k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) | ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p} ⊆ V) := by sorry
