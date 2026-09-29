-- Prove2me | Theorems.Thm_LocalGL2_Kirillov_exists_isBump
-- name    : LocalGL2.Kirillov.exists_isBump
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/92cd8f50-7a1e-556e-8610-e5c4b10f964c
-- title:
--   Existence of bump functions in the Kirillov space
-- statement:
--   Let $K$ be a number field, $v$ a finite place of $K$, and $F = K_v$ the associated completion, with $G = \mathrm{GL}_2(F)$. Let $\psi$ be an additive character of $F$ with values in $\mathbb{C}$ which is non-trivial and satisfies $\psi t = 1$ for all $t$ in some neighbourhood of $0$. Let $S$ be a $\mathbb{C}$-submodule of the space of functions $G \to \mathbb{C}$ such that (i) $S$ is stable under right translation: for $W \in S$ and $k \in G$ the function $g \mapsto W(gk)$ again lies in $S$; (ii) every $W \in S$ is smooth in the sense that there is an open subgroup $K_0 \le G$ with $g \mapsto W(gk)$ equal to $W$ for all $k \in K_0$. Let $\varpi \in F^\times$ be a uniformiser, i.e. $\mathrm{v}(\varpi) = \exp(-1)$ for the valuation of $F$, let $\delta$ be a unit of $\mathrm{WithZero}(\mathrm{Multiplicative}\,\mathbb{Z})$, let $n$ be an integer, and let $\tau$ be a character in [`LocalGL2.Kirillov.Ch v δ`](def/LocalGL2_Kirillov.html#L386), that is, an additive character of $\mathrm{Additive}(\mathrm{Qm}\ v\ \delta)$ with values in $\mathbb{C}$. Write `defectSpan` for the $\mathbb{C}$-span of the functions $(g \mapsto U(g \cdot \mathrm{unipotentGL2}\ x)) - \psi(x)\, U$ with $U \in S$ and $x \in F$, and let $\xi$ be an element of the quotient $(G \to \mathbb{C})/\mathrm{defectSpan}$ lying in the image `coinv` of $S$ under the quotient map. The assertion is that there exists $E \in S$ which is a bump for these data: for every integer $k$ and every $u \in \mathrm{UF}\ v$, the Kirillov value `shell v ψ S ϖ E k u`, namely `kirillov v ψ S E (ϖ ^ k * u)`, equals $(\mathrm{chv}\ \tau\ u) \cdot \xi$ when $k = n$ and $0$ otherwise.
--
--   This is the first assertion of Proposition 2.9 of Jacquet–Langlands, that the Kirillov space of $S$ contains the functions supported on a single shell $\varpi^n \mathrm{UF}$ on which it is a given character times a fixed co-invariant vector, formulated for a right-translation-stable space $S$ of smooth functions and with the $\psi$-twisted co-invariants not assumed one-dimensional. It feeds the Rankin–Selberg step used in the Langlands–Tunnell input to the argument, through [`LanglandsTunnell.RankinSelberg.exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne`](thm.html#LanglandsTunnell.RankinSelberg.exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_Kirillov_exists_isBump.lean

import Mathlib
import Definitions.Def_LocalGL2_Kirillov

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LocalGL2.Kirillov.exists_isBump
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ψ : AddChar (v.adicCompletion K) ℂ) (hψ : ψ ≠ 1)
    (hψ0 : ∀ᶠ t in nhds (0 : v.adicCompletion K), ψ t = 1)
    (S : Submodule ℂ (GL (Fin 2) (v.adicCompletion K) → ℂ))
    (hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (v.adicCompletion K), (fun g => W (g * k)) ∈ S)
    (hsm : ∀ W ∈ S, ∃ K₀ : Subgroup (GL (Fin 2) (v.adicCompletion K)),
      IsOpen (K₀ : Set (GL (Fin 2) (v.adicCompletion K))) ∧ ∀ k ∈ K₀, (fun g => W (g * k)) = W)
    (ϖ : (v.adicCompletion K)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (δ : (WithZero (Multiplicative ℤ))ˣ) (n : ℤ) (τ : LocalGL2.Kirillov.Ch v δ)
    (ξ : (GL (Fin 2) (v.adicCompletion K) → ℂ) ⧸ LocalGL2.Kirillov.defectSpan v ψ S)
    (hξ : ξ ∈ LocalGL2.Kirillov.coinv v ψ S) :
    ∃ E ∈ S, LocalGL2.Kirillov.IsBump v ψ S ϖ n τ ξ E := by sorry
