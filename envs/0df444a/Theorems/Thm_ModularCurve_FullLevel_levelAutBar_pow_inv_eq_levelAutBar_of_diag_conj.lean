-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj
-- name    : ModularCurve.FullLevel.levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/0692e32d-56b6-5995-a82f-aafa2b43f6e1
-- title:
--   Level automorphisms under diagonal conjugation modulo q
-- statement:
--   Fix a prime $q$ and a natural number $M'$ with $q \nmid M'$, and let $\zeta$ be an element of `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Let $d \in (\mathbb{Z}/q)^{\times}$ and let $\alpha, \alpha' \in \mathrm{SL}_2(\mathbb{Z})$ both lie in $\Gamma_0(M')$. Assume that, after entrywise reduction of integer matrices modulo $q$, $$\begin{pmatrix}1&0\\0&d\end{pmatrix}\bar{\alpha} = \bar{\alpha'}\begin{pmatrix}1&0\\0&d\end{pmatrix}$$ holds in $M_2(\mathbb{Z}/q)$. Then `levelAutBar q M'` takes the same value at the pair $(\zeta^{m}, \alpha)$, where $m$ is the canonical representative of $d^{-1}$ in $\mathbb{Z}/q$ (the root of unity produced by `Idx.pow`), as it does at the pair $(\zeta, \alpha')$. Here `levelAutBar q M' ζ γ` is, by definition, a classically chosen $\overline{\mathbb{Q}}$-algebra automorphism $\tau$ of the intermediate field `fieldBar q M'` $=$ `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')` of $\overline{\mathbb{Q}}$-Laurent series satisfying `IsLevelAutBar q M' ζ γ` when such a $\tau$ exists, and the identity otherwise; the defining property is that for every weight $k$, all modular forms $f,g$ of weight $k$ on [`CohCarrier.GammaH (q ^ 2 * M') (levelH q M')`](def/CohCarrier_Level.html#L133) with integral $q$-expansions $p_f,p_g$ and $p_g$ having nonzero associated series, and every ring embedding $\iota \colon \overline{\mathbb{Q}} \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$, the image under $\iota$ of $\tau(p_f/p_g)$ times the $q$-expansion of $g \mid_k \mathrm{conjElem}\, q\, \gamma$ equals the $q$-expansion of $f \mid_k \mathrm{conjElem}\, q\, \gamma$.
--
--   This is the form of Shimura's reciprocity law needed to compare level automorphisms across the geometric components of the full level $q$ curve over $\Gamma_0(M')$: conjugating $\alpha$ by $\mathrm{diag}(1,d)$ modulo $q$ is matched by replacing the component $\zeta$ by $\zeta^{d^{-1}}$. It is used in the proof that the automorphisms `levelAutBar q M' ζ γ` generate a finite subgroup, and in the computations of inertia at the cusp of the Igusa curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj (q : ℕ) [Fact q.Prime]
    (M' : ℕ) (hqM' : ¬ q ∣ M') (ζ : ModularCurve.FullLevel.Idx q) (d : (ZMod q)ˣ) (α α' : SL(2, ℤ))
    (hα : α ∈ CongruenceSubgroup.Gamma0 M') (hα' : α' ∈ CongruenceSubgroup.Gamma0 M')
    (h : !![(1 : ZMod q), 0; 0, (d : ZMod q)] * (α : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q)
        = (α' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) * !![(1 : ZMod q), 0; 0, (d : ZMod q)]) :
    ModularCurve.FullLevel.levelAutBar q M' (ζ.pow d⁻¹) α =
      ModularCurve.FullLevel.levelAutBar q M' ζ α' := by sorry
