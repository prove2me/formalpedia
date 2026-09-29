-- Prove2me | Theorems.Thm_LocalGL2_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span
-- name    : LocalGL2.exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/3d167894-7eea-5135-b809-30931eac179a
-- title:
--   Multiplying a Kirillov function by the indicator of a ball
-- statement:
--   Let $K$ be a number field, $v$ a height-one prime of its ring of integers $\mathcal{O}_K$, and $K_v$ the $v$-adic completion with its valuation $\mathrm{Valued.v}$ taking values in $\mathbb{Z}^{\mathrm{mult}}\cup\{0\}$. Let $\psi$ be an additive character $K_v \to \mathbb{C}$ which is non-trivial and equal to $1$ on some neighbourhood of $0$. Let $S$ be a $\mathbb{C}$-submodule of the space of all functions $\mathrm{GL}_2(K_v) \to \mathbb{C}$ that is stable under right translation, i.e. $g \mapsto U(gk)$ lies in $S$ for every $U \in S$ and every $k \in \mathrm{GL}_2(K_v)$. Let $W \in S$ be right invariant under some open subgroup $K_0 \le \mathrm{GL}_2(K_v)$, meaning $g \mapsto W(gk)$ equals $W$ for all $k \in K_0$. Let $a_0 \in K_v$ and let $\delta$ be a unit of $\mathbb{Z}^{\mathrm{mult}}\cup\{0\}$. Write $D$ for the $\mathbb{C}$-span of the functions $\bigl(g \mapsto U(g\,n(x))\bigr) - \psi(x)\,U$, where $U$ ranges over $S$, $x$ over $K_v$, and $n(x) \in \mathrm{GL}_2(K_v)$ is the unipotent matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ (with inverse $n(-x)$). The assertion is that there exists $W' \in S$ such that for every $t \in \mathrm{GL}_2(K_v)$ whose underlying matrix has $t_{01} = t_{10} = 0$ and $t_{11} = 1$: if $\mathrm{v}(t_{00} - a_0) < \delta$ then $\bigl(g \mapsto W'(gt)\bigr) - \bigl(g \mapsto W(gt)\bigr) \in D$, and otherwise $\bigl(g \mapsto W'(gt)\bigr) \in D$.
--
--   In the language of Kirillov theory for $\mathrm{GL}_2$ over a local field, the conclusion says that the Kirillov function of $W'$, with values in the $\psi$-twisted coinvariants $S/D$, is the Kirillov function of $W$ multiplied by the indicator function of the ball $\{a : \mathrm{v}(a - a_0) < \delta\}$; no transformation law for members of $S$ and no smoothness beyond that of $W$ itself is assumed. It is used in the construction of bump functions ([`LocalGL2.Kirillov.exists_isBump`](thm.html#LocalGL2.Kirillov.exists_isBump)) on the way to identifying the compactly supported locally constant functions inside the space of Kirillov functions of $S$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LocalGL2.exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ψ : AddChar (v.adicCompletion K) ℂ) (hψ : ψ ≠ 1)
    (hψ0 : ∀ᶠ t in nhds (0 : v.adicCompletion K), ψ t = 1)
    (S : Submodule ℂ (GL (Fin 2) (v.adicCompletion K) → ℂ))
    (hstab : ∀ U ∈ S, ∀ k : GL (Fin 2) (v.adicCompletion K), (fun g => U (g * k)) ∈ S)
    (W : GL (Fin 2) (v.adicCompletion K) → ℂ) (hW : W ∈ S)
    (hsmW : ∃ K₀ : Subgroup (GL (Fin 2) (v.adicCompletion K)),
      IsOpen (K₀ : Set (GL (Fin 2) (v.adicCompletion K))) ∧ ∀ k ∈ K₀, (fun g => W (g * k)) = W)
    (a₀ : v.adicCompletion K) (δ : (WithZero (Multiplicative ℤ))ˣ) :
    ∃ W' ∈ S, ∀ t : GL (Fin 2) (v.adicCompletion K),
      (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = 1 →
      (Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 - a₀) < (δ : WithZero (Multiplicative ℤ)) →
        (fun g => W' (g * t)) - (fun g => W (g * t)) ∈ Submodule.span ℂ
        {V : GL (Fin 2) (v.adicCompletion K) → ℂ | ∃ U ∈ S, ∃ x : v.adicCompletion K,
          V = (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - ψ x • U}) ∧
      (¬ Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 - a₀) < (δ : WithZero (Multiplicative ℤ)) →
        (fun g => W' (g * t)) ∈ Submodule.span ℂ
        {V : GL (Fin 2) (v.adicCompletion K) → ℂ | ∃ U ∈ S, ∃ x : v.adicCompletion K,
          V = (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - ψ x • U}) := by sorry
