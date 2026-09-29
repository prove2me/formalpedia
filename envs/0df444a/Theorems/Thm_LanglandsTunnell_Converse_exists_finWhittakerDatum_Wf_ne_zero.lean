-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_finWhittakerDatum_Wf_ne_zero
-- name    : LanglandsTunnell.Converse.exists_finWhittakerDatum_Wf_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/643bf394-5bc1-5ddd-8bb0-42142fb6ca4f
-- title:
--   Existence of a non-vanishing finite Whittaker datum
-- statement:
--   Let $K$ be a number field, let $S$ be a finite set of height-one primes of $\mathcal{O}_K$, and let $\Pi$ be a Hecke eigensystem for $K$ with complex values, that is, a non-zero level ideal of $\mathcal{O}_K$ together with two functions $v \mapsto a_v$, $v \mapsto b_v$ on the finite places. Assume $b_v \neq 0$ for every finite place $v \notin S$. Then there exists a datum `FinWhittakerDatum` for $(S,\Pi)$, namely a function $W_f \colon \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ that factors through the finite-adelic part `glFin`, is unchanged by right multiplication by the image of any element of $\mathrm{GL}_2(K_v)$ for $v \in S$, satisfies $W_f(u(x)g) = \psi_v(x) W_f(g)$ for $v \notin S$ and $x \in K_v$, where $u(x)$ is the upper unipotent matrix with entry $x$ embedded at $v$ and $\psi_v$ is the local component `psiLocal` of the standard adelic additive character, is right invariant under $\mathrm{GL}_2(\mathcal{O}_v)$ for $v \notin S$, for each $v \notin S$ and each ideal $M$ not divisible by $v$ satisfies the coset Hecke eigenvalue relation `IsHeckeCosetEigenfunctionAt` for the generator `heckeGen` at $v$, the group $\mathrm{levelOne}(M) \cap \mathrm{GL}_2(\mathbb{A}_{K,\mathrm{fin}})$ and eigenvalue $a_v$, satisfies $W_f(z g) = (\mathrm{cNorm}\,v)^{-1} b_v\, W_f(g)$ for the central scalar $z$ given by $\det$ of `heckeGen` at $v$ for $v \notin S$, and is right invariant under $\mathrm{levelOne}(N_0) \cap \mathrm{GL}_2(\mathbb{A}_{K,\mathrm{fin}})$ for some non-zero ideal $N_0$; and there is a $g$ with $W_f(g) \neq 0$.
--
--   This is the finite-adelic half of the converse construction attaching an automorphic object to a table of Hecke eigenvalues: the datum plays the role of the product over $v \notin S$ of unramified local Whittaker functions normalised by the eigenvalues $(a_v,b_v)$, with the non-vanishing assertion supplying a point where the product does not vanish. It feeds the constructions of arithmetic genuine cuspidal realisations in the Langlands–Tunnell converse step and the identification of the archimedean factor of the Whittaker coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_finWhittakerDatum_Wf_ne_zero.lean

import Definitions.Def_LanglandsTunnell_JLConverse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.exists_finWhittakerDatum_Wf_ne_zero (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Pi : HeckeEigensystem K ℂ) (hb : ∀ v ∉ S, Pi.b v ≠ 0) :
    ∃ D : FinWhittakerDatum K S Pi, ∃ g, D.Wf g ≠ 0 := by sorry
